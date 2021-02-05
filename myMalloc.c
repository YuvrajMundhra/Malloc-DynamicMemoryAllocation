#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;


/**
 * My helper functions
 *
 */

//Helper function round the size to 8 bytes
static size_t roundSize(size_t);

//searches the freelist to get the block of appropriate size
static header * searchFreelist(size_t);

//removes the header from a freelist
static void removeHeader(header *);
static void removeHeader2param(header *, header *);

//splits the new block if has extra bytes and adjusts free lists
static header * splitBlock(header *, size_t);

//inserting header into the beginning of given free list index
static void insertHeader(header *, size_t);

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  (void) raw_size;
  //assert(false);
  //exit(1);
  //return null if 0 bytes asked
  if(raw_size == 0) {
    return NULL;
  }
  //calling function to round size to multiple of 8
  size_t rounded_raw_size = roundSize(raw_size);

  //calculate actual size = metadata + rounded_size
  size_t actual_size = ALLOC_HEADER_SIZE + rounded_raw_size;

  //get appropriate header, set state to allocated, return block after header
  header * requiredHdr = searchFreelist(rounded_raw_size);
  set_state(requiredHdr, ALLOCATED);
  //return requiredHdr->data;
  return requiredHdr + ALLOC_HEADER_SIZE;
}


/**
 * @brief Helper function round the raw_size to multiple of 8
 * 
 * @param raw_size number of bytes the user needs
 *
 * @return raw_size rounded to multiple of 8
 */
static size_t roundSize(size_t raw_size) {
  size_t rounded_raw_size;
  if(raw_size % 8 != 0) {
    size_t modulo_raw_size = raw_size % 8;
    rounded_raw_size = raw_size + (8 - modulo_raw_size);
  } else {
    rounded_raw_size = raw_size;
  }

  //make rounded raw bytes minimum 16 bytes
  if(rounded_raw_size < 16) {
    rounded_raw_size = 16;
  }
  return rounded_raw_size;
}


/**
 * @brief Helper function searches the freelist to get block
 * calls functions to remove header from free list and split
 *
 * @param rounded_raw_size
 *
 * @return the pointer to the start of the block(after header)
 */
static header * searchFreelist(size_t rounded_raw_size) {
  header * requiredHdr;
  size_t freelistIndex = (rounded_raw_size/8) - 1;
  
  //traverses through the available indexes except last one until finds free list
  if(freelistIndex < N_LISTS - 1) {
    for(int i = freelistIndex; i < N_LISTS - 1; i++) {
      header * freelist = &freelistSentinels[i];

      //if free list empty continue to next freelist
      if(freelist->next == freelist) {
        continue;
      } else {
        requiredHdr = freelist->next;
	size_t sizeofBlock = get_size(requiredHdr);

	//check to see if need to split the block
	if(sizeofBlock - ALLOC_HEADER_SIZE == rounded_raw_size) {
	  removeHeader(freelist);
	  return requiredHdr;
	} else if(sizeofBlock - ALLOC_HEADER_SIZE > rounded_raw_size) {
	  //split the block
	  header * new_Hdr = splitBlock(requiredHdr, rounded_raw_size + ALLOC_HEADER_SIZE); 
	  return new_Hdr;
	}
      }
    }
  }

  //iterating through last freelist to find appropriate size
  header * freelist = &freelistSentinels[N_LISTS-1];
  header * current_hdr = freelist->next;

  size_t current_hdr_size = get_size(current_hdr);
  printf("%d", current_hdr_size);
  while(current_hdr != freelist) {
    if(get_size(current_hdr) - ALLOC_HEADER_SIZE == rounded_raw_size) {
      removeHeader2param(freelist, current_hdr);
      return current_hdr;
    } else if(get_size(current_hdr) - ALLOC_HEADER_SIZE > rounded_raw_size) {
      header * new_hdr = splitBlock(current_hdr, rounded_raw_size + ALLOC_HEADER_SIZE);
      return new_hdr;
    }
    
    current_hdr = current_hdr->next;
  }

  //request chunk
}



/**
 * @brief Helper function to split the block and adjust the new blocks free list
 *
 * @param Pointer to required header, perfect size of the block needed
 *
 * @return pointer to new header of the required size
 */
static header * splitBlock(header * requiredHdr, size_t actual_required_size) {
  //creating pointer for new header
  size_t size_required_block = get_size(requiredHdr);
  void * new_hdr_ptr = requiredHdr + size_required_block - actual_required_size;
  header * new_hdr = (header *) (char *)new_hdr_ptr;
  
  //setting new header's attributes
  set_state(new_hdr, UNALLOCATED);
  set_size(new_hdr, actual_required_size);
  new_hdr->left_size = size_required_block - actual_required_size;

  //changing the remainder block size (left block)
  set_size(requiredHdr, size_required_block - actual_required_size);

  //update left size of next block to new hdr
  header * right_header = get_right_header(new_hdr);
  
  //checkkkkkkkkkkk, what if right is fencepost
  right_header->left_size = get_size(new_hdr);
  
  
  //Changing freelist for remainder of the block
  size_t prev_index = (size_required_block - ALLOC_HEADER_SIZE)/8 - 1;
  size_t new_index = (get_size(requiredHdr) - ALLOC_HEADER_SIZE)/8 - 1;

  if(prev_index == new_index) {
    //no need to removeHdr
    return new_hdr;
  } else {
    //removing header from free list
    header * freelist = &freelistSentinels[prev_index];
    removeHeader2param(freelist, requiredHdr);

    //inserting the left block into a new free list
    insertHeader(requiredHdr, new_index);

    return new_hdr;  
  }
}


/**
 * @brief Helper function to remove next header from the given freelist
 *
 * @param freelist pointer
 *
 * @return void (just removes header)
 */

static void removeHeader(header * freelist) {
  header * deletingHdr = freelist->next;
  
  if(deletingHdr->next == freelist) {
    freelist->next = freelist;
    freelist->prev = freelist;
  } else {
    freelist->next = deletingHdr->next;
    deletingHdr->next->prev = freelist;
  }
}

/**
 * @brief helper function to remove header from freelist that is not at the beginning
 *
 * @param freelist, pointer to header to be deleted
 *
 * @return void (just removes header)
 */

static void removeHeader2param(header * freelist, header * deletingHdr) {
  if(deletingHdr->next == freelist) {
    freelist->prev = deletingHdr->prev;
    deletingHdr->prev->next = freelist;
  } else {
    header * deletingHdr_prev = deletingHdr->prev;
    header * deletingHdr_next = deletingHdr->next;
    deletingHdr_prev->next = deletingHdr_next;
    deletingHdr_next->prev = deletingHdr_prev;
  }
}


/**
 * @brief Helper function to insert the header into a new freelist
 *
 * @param header pointer, new freelist index
 *
 * @return void (just inserts header)
 */

static void insertHeader(header * insertHdr, size_t index) {
  if(index >= N_LISTS) {
    index = N_LISTS-1;
  }
  header * freelist = &freelistSentinels[index];
  
  //update left size
  if(freelist->next == freelist) {
    freelist->next = insertHdr;
    freelist->prev = insertHdr;
    insertHdr->next = freelist;
    insertHdr->prev = freelist;
  } else {
    header * current_next = freelist->next;
    freelist->next = insertHdr;
    insertHdr->next = current_next;
    insertHdr->prev = freelist;
    current_next->prev = insertHdr;
  }
}


/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  (void) p;
  //assert(false);
  //exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
