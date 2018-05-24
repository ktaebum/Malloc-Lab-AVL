/*
 * Taebum Kim stu119 2013-10942
 * phya.ktaebum@gmail.com
 * k.taebum@snu.ac.kr
 */

/*
 * My memory allocator using AVL Tree
 *
 * Heap structure
 *
 * Begin
 * ---------------------------------------------------------------------
 *  NumTree Words. Each corresponds to root of each avl tree
 * ---------------------------------------------------------------------
 *  PAD
 * ---------------------------------------------------------------------
 *  Prologue Header
 * ---------------------------------------------------------------------
 *  Prologue Footer
 * ---------------------------------------------------------------------
 *  Allocatable Space (Real Heap)
 * ---------------------------------------------------------------------
 *  Epilogue
 * ---------------------------------------------------------------------
 * End
 *
 * AVL Tree Implementation
 *
 * Each tree index covers size...
 *
 * 0: 2^0 to 2^1
 * 1: 2^1 to 2^2
 * 2: 2^2 to 2^3
 * 3: 2^3 to 2^4
 * 4: 2^4 to 2^5
 * 5: 2^5 to 2^6
 * 6: 2^6 to 2^7
 * 7: 2^7 to 2^8
 * 8: 2^8 to 2^9
 * 9: 2^9 to 2^10
 * 10: 2^10 to 2^11
 * 11: 2^11 to 2^12
 * 12: 2^12 to 2^13
 * 13: 2^13 to 2^14
 * 14: 2^14 to 2^15
 * 15: 2^15 to 2^16
 * 16: 2^16 to 2^17
 * 17: 2^17 to 2^18
 * 18: 2^18 to 2^19
 * 19: 2^19 to size_t MAX
 * All sizes are multiplied by MINIMUM_BLOCK_SIZE
 * since there are no free blocks whose size < MINIMUM_BLOCK_SIZE
 *
 * Compare key is address of block (helps lower fragmentation)
 *
 * Each node is composed with 24 bytes (6 Words)
 *
 * Node Begin
 * ------------------------------- 0
 *  Header
 * ------------------------------- 4
 *  Left Child Pointer
 * ------------------------------- 8
 *  Right Child Pointer
 * ------------------------------- 12
 *  Height Value
 * ------------------------------- 16
 *  Pad
 * ------------------------------- 20
 *  Footer
 * ------------------------------- 24
 * Node End
 *
 */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

#ifndef DEBUG
#define checkAll()
#else
#define checkAll() mm_check()
#endif

#define WSIZE 4                 // word and header/footer size (bytes)
#define DSIZE 8                 // double word size
#define CHUNKSIZE (1 << 12)     // extend heap by 4096 bytes
#define REALLOC_BOUND (1 << 7)  // coalesce lower bound in realloc
#define MINIMUM_BLOCK_SIZE 24   // minimum block size
#define NUM_TREE 20             // number of avl trees

/* flags in extend Heap */
#define DIRECT_RETURN 1  // return directly after extend heap (use in realloc)
#define COALESCE_RETURN 2  // return after coalesce (normal case)

/* Return value for allocate position */
#define ALLOCATE_FROM_BACK 1
#define ALLOCATE_FROM_FRONT 2
#define ALLOCATE_WHOLE_BLOCK 3

/*
 * Some Useful Macros
 */

/* Get Max value */
#define MAX(x, y) ((x > y) ? (x) : (y))

/* pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* read and write a word */
#define GET(p) (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (val))

/* read the size and allocated flag */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HEADER(ptr) ((char *) (ptr) -WSIZE)
#define FOOTER(ptr) ((char *) (ptr) + GET_SIZE(HEADER(ptr)) - DSIZE)

/* get next block and prev block */
#define NEXT_BLOCK(ptr) ((char *) (ptr) + GET_SIZE(((char *) (ptr) -WSIZE)))
#define PREV_BLOCK(ptr) ((char *) (ptr) -GET_SIZE(((char *) (ptr) -DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))  // 8 bytes

/*
 * same as PUT but, for set pointer, and better readability
 * for avoid warning, case into uintptr_t
 */
#define SET_PTR(ptr, p) (*((unsigned int *) (ptr)) = (uintptr_t)(p))
#define GET_PTR(ptr) ((void *) (uintptr_t) GET(ptr))

/* get left child address */
#define LEFT_CHILD(ptr) ((char *) (ptr))

/* get right child address */
#define RIGHT_CHILD(ptr) ((char *) (ptr) + WSIZE)

/* get height */
#define HEIGHT(ptr) ((char *) (ptr) + 2 * WSIZE)
#define GET_HEIGHT(ptr) ((ptr == NULL) ? 0 : GET(HEIGHT(ptr)))

/* Return status, or exit code for heap checker */
#define OK 0
#define NOT_ALL_FREE_BLOCKS_IN_TREE 1
#define NOT_ALL_TREES_ARE_BALANCED 2
#define NOT_ALL_FREE_BLOCKS_SORTED_BY_ADDRESS 3
#define NOT_COALESCED_BLOCK_EXIST 4
#define NOT_ALL_FREE_BLOCK_MARKED_AS_FREE 5
#define NOT_ALL_TREE_NODE_IN_PROPER_TREE 6
#define NOT_ALL_BLOCKS_BIGGER_THAN_MIN_BLOCK_SIZE 7

static char *heap_listp = NULL;      // point prologue block
static void *segregated_avl = NULL;  // point start of segregated_avls

static size_t maxAllocatedSize = 0;            // maximum Allocated Size
static size_t minAllocatedSize = ~(size_t) 0;  // minimum Allocated Size

static int checker = 1;  // global static variable for heap checker functions

/* here comes static inline helper functions for tree */

static inline void *getTree(int index) {
  /* Get index-th tree */
  return (void *) (segregated_avl) + (index * WSIZE);
}

static inline void updateHeight(void *node) {
  /* Update height of given node */
  unsigned int leftHeight = GET_HEIGHT(GET_PTR(LEFT_CHILD(node)));
  unsigned int rightHeight = GET_HEIGHT(GET_PTR(RIGHT_CHILD(node)));

  PUT(HEIGHT(node), 1 + MAX(leftHeight, rightHeight));
}

static inline void *getSmallestBlock(void *root) {
  /*
   * Get smallest (lowest address) w.r.t given node (root)
   * Use at deleteBlock
   */
  void *left;
  while ((left = GET_PTR(LEFT_CHILD(root))) != NULL) { root = left; }
  return root;
}

static inline void *rightRotate(void *root) {
  /* right rotate root node */
  void *leftChild = GET_PTR(LEFT_CHILD(root));
  void *leftRightChild = GET_PTR(RIGHT_CHILD(leftChild));

  SET_PTR(RIGHT_CHILD(leftChild), root);
  SET_PTR(LEFT_CHILD(root), leftRightChild);

  updateHeight(root);
  updateHeight(leftChild);

  return leftChild;
}

static inline void *leftRotate(void *root) {
  /* left rotate root node */
  void *rightChild = GET_PTR(RIGHT_CHILD(root));
  void *rightLeftChild = GET_PTR(LEFT_CHILD(rightChild));

  SET_PTR(LEFT_CHILD(rightChild), root);
  SET_PTR(RIGHT_CHILD(root), rightLeftChild);

  updateHeight(root);
  updateHeight(rightChild);

  return rightChild;
}

static inline void *doubleLeftRotate(void *root) {
  /* Double left rotate root node */
  void *right = GET_PTR(RIGHT_CHILD(root));
  SET_PTR(RIGHT_CHILD(root), rightRotate(right));
  return leftRotate(root);
}

static inline void *doubleRightRotate(void *root) {
  /* Double right rotate root node */
  void *left = GET_PTR(LEFT_CHILD(root));
  SET_PTR(LEFT_CHILD(root), leftRotate(left));
  return rightRotate(root);
}

static inline void *makeBalance(void *root) {
  /* Make balanced root node using rotation */
  void *leftChild = GET_PTR(LEFT_CHILD(root));
  void *rightChild = GET_PTR(RIGHT_CHILD(root));

  int leftHeight = (int) GET_HEIGHT(leftChild);
  int rightHeight = (int) GET_HEIGHT(rightChild);

  if (leftHeight - rightHeight == 2) {
    // left heavy
    if (GET_HEIGHT(GET_PTR(RIGHT_CHILD(leftChild))) >
        GET_HEIGHT(GET_PTR(LEFT_CHILD(leftChild)))) {
      // double rotation case
      root = doubleRightRotate(root);
    } else {
      root = rightRotate(root);
    }
  }

  if (rightHeight - leftHeight == 2) {
    // right heavy
    if (GET_HEIGHT(GET_PTR(LEFT_CHILD(rightChild))) >
        GET_HEIGHT(GET_PTR(RIGHT_CHILD(rightChild)))) {
      // double rotation case
      root = doubleLeftRotate(root);
    } else {
      root = leftRotate(root);
    }
  }

  return root;
}

static inline int findTreeIndex(size_t size) {
  /* Find avl-tree index w.r.t to given size */
  int index = 0;
  size_t value = MINIMUM_BLOCK_SIZE;
  while (index < NUM_TREE - 1) {
    if (size >= value && size < value * 2) { break; }
    index++;
    value <<= 1;
  }
  return index;
}

static inline void initTreeNode(void *ptr, size_t size) {
  /* Initialize Free Block Tree Node
   *	left = NULL
   *	right = NULL
   *	height = 1
   * */
  if (size < MINIMUM_BLOCK_SIZE) {
    /* Free block cannot be smaller than MINIMUM_BLOCK_SIZE */
    fprintf(stderr,
            "Block size (%zu) should be greater or equal than %d\n",
            size,
            MINIMUM_BLOCK_SIZE);
    exit(1);
  }

  PUT(HEADER(ptr), PACK(size, 0));
  PUT(FOOTER(ptr), PACK(size, 0));
  SET_PTR(RIGHT_CHILD(ptr), NULL);
  SET_PTR(LEFT_CHILD(ptr), NULL);
  PUT(HEIGHT(ptr), 1);
}

static inline int defindeAllocateSplitPosition(size_t ptrSize,
                                               size_t targetSize) {
  /*
   * define split position
   * could be from front, back, or whole
   *
   * if size after truncate >= MINIMUM_BLOCK_SIZE, cut
   * keep track minAllocatedBlockSize, and maxAllocatedBlockSize
   * if targetSize is closer to min, allocate from front
   * else, allocate from back
   *
   * this helps reduce internal fragmentation since it is kind of binary
   * classifier
   *
   * group similiar sized block together in either front or back side of heap
   *
   * else return whole
   */

  if (ptrSize >= targetSize + MINIMUM_BLOCK_SIZE) {
    if (targetSize > maxAllocatedSize) {
      // allocate from back
      maxAllocatedSize = targetSize;
      if (targetSize < minAllocatedSize) { minAllocatedSize = targetSize; }
      return ALLOCATE_FROM_BACK;
    } else if (targetSize < minAllocatedSize) {
      minAllocatedSize = targetSize;
      if (targetSize > maxAllocatedSize) { maxAllocatedSize = targetSize; }
      return ALLOCATE_FROM_FRONT;
    } else {
      // minAllocatedSize < targetSize < maxAllocatedSize
      // Calculate distance and take closer one
      if ((maxAllocatedSize - targetSize) < (targetSize - minAllocatedSize)) {
        // allocate from back
        return ALLOCATE_FROM_BACK;
      } else {
        return ALLOCATE_FROM_FRONT;
      }
    }
  } else {
    // allocate whole
    if (ptrSize > maxAllocatedSize) { maxAllocatedSize = ptrSize; }
    if (ptrSize < minAllocatedSize) { minAllocatedSize = ptrSize; }

    return ALLOCATE_WHOLE_BLOCK;
  }
}

static inline void printBlockInfo(void *ptr) {
  /* Print Block Information,
   * For debugging  */
  printf("Block address = %p\n", ptr);
  printf("Block Size (Header) = %u\n", GET_SIZE(HEADER(ptr)));
  printf("Block Allocated (Header) = %d\n", GET_ALLOC(HEADER(ptr)));
  printf("Block Size (Header) = %u\n", GET_SIZE(FOOTER(ptr)));
  printf("Block Allocated (Header) = %d\n", GET_ALLOC(FOOTER(ptr)));
  printf("Left Address = %p\n", GET_PTR(LEFT_CHILD(ptr)));
  printf("Right Address = %p\n", GET_PTR(RIGHT_CHILD(ptr)));
  printf("Next Block Address = %p\n", NEXT_BLOCK(ptr));
  printf("Prev Block Address = %p\n", PREV_BLOCK(ptr));
}

/* prototypes for static functions */
static void *extendHeap(size_t words, int flags);
static void *coalesce(void *ptr);
static void insertFreeBlock(void *ptr, size_t size);
static void *insertFreeBlock_(void *root, void *ptr);

static void *findFreeBlock(size_t targetSize);
static void findFreeBlock_(void *root,
                           size_t targetSize,
                           void **allocateBlock);

static void *splitAndPlace(void *ptr, size_t targetSize);
static void *reallocSplitAndPlace(void *new_ptr,
                                  size_t newSize,
                                  size_t oldSize);

static void deleteBlock(void *ptr);
static void *deleteBlock_(void *root, void *ptr);

/* functions for heap checker */
static void checkAllFreeBlocksInTree();
static void checkAllFreeBlocksInTree_(void *root, void *ptr);
static void checkAllTreesBalanced();
static void checkAllTreesBalanced_(void *root);
static void checkAllTreesOrderedByAddress();
static void checkAllTreesOrderedByAddress_(void *root, void *previous);
static void checkNoPossibleCoalesceBlocks();
static void checkEveryFreeBlockMarkedAsFree();
static void checkEveryFreeBlockMarkedAsFree_(void *root);
static void checkEveryTreeNodeInProperTree();
static void checkEveryTreeNodeInProperTree_(void *root,
                                            size_t minSize,
                                            size_t maxSize);
static void checkEveryBlocksBiggerThanMIN_BLOCK_SIZE();
static void printTree();
static void printTree_(void *root, unsigned int indent);

int mm_check(void) {
  // heap checker
  // Must pass all! (called when each mm_malloc, mm_free, mm_realloc ends)
  checkAllFreeBlocksInTree();
  checkAllTreesBalanced();
  checkAllTreesOrderedByAddress();
  checkNoPossibleCoalesceBlocks();
  checkEveryFreeBlockMarkedAsFree();
  checkEveryTreeNodeInProperTree();
  checkEveryBlocksBiggerThanMIN_BLOCK_SIZE();

  printTree();
  return OK;
}

/*
 * mm_init - initialize the malloc package.
 *
 * perform any necessary initializations, such as allocating the initial heap
 * area. Return value should be -1 if there was a problem in performing the
 * initialization.
 */
int mm_init(void) {
  /*
   * Initialize global static pointers
   * 	heap_listp: start point of heap
   * 	segregated_avl: start point of segregated avl roots
   *
   * Initialize global variable
   *  maxAllocatedSize = 0
   *  minAllocatedSize = ~(size_t) 0
   */
  if ((segregated_avl = mem_sbrk(NUM_TREE * WSIZE)) == (void *) -1) {
    /* fail to initialize segregated_avl roots */
    return -1;
  }

  for (int i = 0; i < NUM_TREE; i++) {
    /* Initialize each avl root as NULL */
    void *root = (void *) (segregated_avl) + i * WSIZE;
    SET_PTR(root, NULL);
  }

  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1) {
    // failed to initialize
    return -1;
  }

  PUT(heap_listp, 0);                             // initial pad block
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // epilogue block

  heap_listp += (2 * WSIZE);  // pointing prologue footer

  /* Initialize global static variables */
  maxAllocatedSize = 0;
  minAllocatedSize = ~(size_t) 0;

  return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
  if (size == 0) {
    // return NULL exactly
    return NULL;
  }

  size_t alignedSize =
      MAX(ALIGN(size + SIZE_T_SIZE), MINIMUM_BLOCK_SIZE);  // make alignment

  void *ptr = NULL;

  if ((ptr = findFreeBlock(alignedSize)) != NULL) {
    // success to find directly
    checkAll();
    return ptr;
  } else {
    // fail to find, extend heap
    size_t extendSize = MAX(alignedSize, CHUNKSIZE);
    if ((ptr = extendHeap(extendSize / WSIZE, COALESCE_RETURN)) == NULL) {
      // fail to extend
      return NULL;
    }

    ptr = splitAndPlace(ptr, alignedSize);
    checkAll();
    return ptr;
  }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
  size_t size = GET_SIZE(HEADER(ptr));
  PUT(HEADER(ptr), PACK(size, 0));
  PUT(FOOTER(ptr), PACK(size, 0));

  coalesce(ptr);
  checkAll();
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  if (ptr == NULL) {
    /* same as mm_malloc */
    return mm_malloc(size);
  }

  if (size == 0) {
    // same as free
    mm_free(ptr);
    return NULL;
  }

  void *old_ptr = ptr;
  size_t oldSize = GET_SIZE(HEADER(old_ptr));

  void *new_ptr = NULL;
  size_t newSize = MAX(ALIGN(size + SIZE_T_SIZE), MINIMUM_BLOCK_SIZE);

  if (newSize < oldSize) {
    new_ptr = reallocSplitAndPlace(old_ptr, newSize, oldSize);
    checkAll();
    return new_ptr;
  } else if (newSize == oldSize) {
    return ptr;
  } else {
    /*
     * Realloc Policy: Check whether we can coalesce previous and next block
     * 1. both free
     * 2. only previous block free
     * 3. only next block free
     * 4. both not free
     *
     * However, when try to coalesce previous block,
     * set lower bound as MAX(minAllocatedBlock, 1 << 7) in my code
     * it force to not coalesce previous block when block size after coalesce
     * previous block becomes smaller that MAX(minAllocatedBlock, 1 << 7)
     *
     * I got intuition from in realloc case, we monotonically increase certain
     * block (like whole storing array) and free other small size array lots
     *
     * Since defineAllocateSplitPosition function's classifier helps large
     * allocate block (close to maxAllocatedSize) be places in back side of
     * heap, and helps small allocate block (close to minAllocatedSize) be
     * places in front side of heap
     *
     * It has high probability to call malloc again with small size
     * So, do not coalesce that lower bound of small size block, left it free
     * for future malloc
     *
     * For nextBlock, if nextBlock is epilogue block,
     * do not call malloc again.
     * Just call extendHeap with small requiredSize as extendHeap(requiredSize,
     * DIRECT_RETURN) DIRECT_RETURN flag prevent coalesce new free block (since
     * it will be allocated directly)
     *
     */
    void *nextBlock = NEXT_BLOCK(ptr);
    void *prevBlock = PREV_BLOCK(ptr);
    int nextAlloc = GET_ALLOC(HEADER(nextBlock));
    int prevAlloc = GET_ALLOC(HEADER(prevBlock));
    size_t nextSize = GET_SIZE(HEADER(nextBlock));
    size_t prevSize = GET_SIZE(HEADER(prevBlock));
    size_t minPrevSize = MAX(minAllocatedSize, REALLOC_BOUND);

    size_t mergedSize = 0;

    if (!prevAlloc && !nextAlloc) {
      mergedSize = (oldSize + nextSize + prevSize);
      if (mergedSize >= newSize) {
        if (mergedSize - prevSize >= minPrevSize) {
          // safe to coalesce previous block
          deleteBlock(prevBlock);
          deleteBlock(nextBlock);
          PUT(HEADER(prevBlock), PACK(mergedSize, 0));
          PUT(FOOTER(prevBlock), PACK(mergedSize, 0));
          memmove(prevBlock, old_ptr, oldSize);
          new_ptr = reallocSplitAndPlace(prevBlock, newSize, oldSize);
          checkAll();
          return new_ptr;
        } else {
          mergedSize -= prevSize;
          if (mergedSize >= newSize) {
            deleteBlock(nextBlock);
            PUT(HEADER(old_ptr), PACK(mergedSize, 0));
            PUT(FOOTER(old_ptr), PACK(mergedSize, 0));
            new_ptr = reallocSplitAndPlace(old_ptr, newSize, oldSize);
            checkAll();
            return new_ptr;
          }
        }
      }
    } else if (!prevAlloc && nextAlloc) {
      mergedSize = (oldSize + prevSize);
      if (mergedSize >= newSize && mergedSize - newSize >= minPrevSize) {
        deleteBlock(prevBlock);
        PUT(HEADER(prevBlock), PACK(mergedSize, 0));
        PUT(FOOTER(prevBlock), PACK(mergedSize, 0));
        memmove(prevBlock, old_ptr, oldSize);
        new_ptr = reallocSplitAndPlace(prevBlock, newSize, oldSize);
        checkAll();
        return new_ptr;
      } else if (nextSize == 0) {
        // give up prevCoalesce. instead, extend heap
        size_t requiredSize = newSize - oldSize;

        /* since we need to extend greater or equal than requiredSize */
        size_t requiredWord = (requiredSize % WSIZE == 0)
                                  ? requiredSize / WSIZE
                                  : (requiredSize / WSIZE + 1);
        void *extended = extendHeap(requiredWord, DIRECT_RETURN);
        mergedSize = GET_SIZE(HEADER(extended)) + oldSize;
        PUT(HEADER(old_ptr), PACK(mergedSize, 0));
        PUT(FOOTER(old_ptr), PACK(mergedSize, 0));
        new_ptr = reallocSplitAndPlace(old_ptr, newSize, oldSize);
        checkAll();
        return new_ptr;
      }
    } else if (prevAlloc && !nextAlloc) {
      mergedSize = (oldSize + nextSize);
      if (mergedSize >= newSize) {
        deleteBlock(nextBlock);
        PUT(HEADER(old_ptr), PACK(mergedSize, 0));
        PUT(FOOTER(old_ptr), PACK(mergedSize, 0));
        new_ptr = reallocSplitAndPlace(old_ptr, newSize, oldSize);
        checkAll();
        return new_ptr;
      }
    } else {
      // prevAlloc && nextAlloc
      if (nextSize == 0) {
        // epilogue hit! extend heap
        size_t requiredSize = newSize - oldSize;
        size_t requiredWord = (requiredSize % WSIZE == 0)
                                  ? requiredSize / WSIZE
                                  : (requiredSize / WSIZE + 1);
        void *extended = extendHeap(requiredWord, DIRECT_RETURN);
        mergedSize = GET_SIZE(HEADER(extended)) + oldSize;
        PUT(HEADER(old_ptr), PACK(mergedSize, 0));
        PUT(FOOTER(old_ptr), PACK(mergedSize, 0));
        new_ptr = reallocSplitAndPlace(old_ptr, newSize, oldSize);
        checkAll();
        return new_ptr;
      }
    }
  }

  /*
   * If reach here, failed to reallocated from given blocks,
   * call mm_malloc
   */

  if ((new_ptr = mm_malloc(size)) == NULL) { return NULL; }

  if (size < oldSize) { oldSize = size; }
  memcpy(new_ptr, old_ptr, oldSize);
  mm_free(old_ptr);

  checkAll();
  return new_ptr;
}

static void *extendHeap(size_t words, int flags) {
  /*
   * Extend Heap by calling mem_sbrk
   * 	words: target extend words number
   * 	flags: return flags
   * 		1. DIRECT_RETURN: return directly after extend (for realloc)
   * 		2. COALESCE_RETURN: return after coalesce
   */
  void *ptr;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long) (ptr = mem_sbrk(size)) == -1) {
    // fail to increase heap size
    return NULL;
  }

  /* Initialize free block header / footer and the epilogue haader */
  PUT(HEADER(ptr), PACK(size, 0));
  PUT(FOOTER(ptr), PACK(size, 0));
  PUT(HEADER(NEXT_BLOCK(ptr)), PACK(0, 1));

  if (flags == COALESCE_RETURN) { ptr = coalesce(ptr); }
  checkAll();
  return ptr;
}

static void *coalesce(void *ptr) {
  /*
   * Coalesce given ptr and insert it to free trees
   * Invariant: ptr is not in free tree
   */

  size_t isPrevBlockAllocated = GET_ALLOC(FOOTER(PREV_BLOCK(ptr)));
  size_t isNextBlockAllocated = GET_ALLOC(HEADER(NEXT_BLOCK(ptr)));

  char *previousBlock = NULL;
  char *nextBlock = NULL;

  size_t mergedSize = GET_SIZE(HEADER(ptr));

  if (isPrevBlockAllocated && isNextBlockAllocated) {
    // cannot coalesce, just insert ptr
    insertFreeBlock(ptr, mergedSize);
  } else if (!isPrevBlockAllocated && isNextBlockAllocated) {
    // merge prevBlock
    previousBlock = PREV_BLOCK(ptr);
    mergedSize += GET_SIZE(HEADER(previousBlock));

    deleteBlock(previousBlock);
    insertFreeBlock(previousBlock, mergedSize);
    ptr = previousBlock;
  } else if (isPrevBlockAllocated && !isNextBlockAllocated) {
    // merge nextBlock
    nextBlock = NEXT_BLOCK(ptr);
    mergedSize += GET_SIZE(HEADER(nextBlock));

    deleteBlock(nextBlock);
    insertFreeBlock(ptr, mergedSize);
  } else {
    // !isPrevBlockAllocated && !isNextBlockAllocated
    // can coalesce all
    previousBlock = PREV_BLOCK(ptr);
    mergedSize += GET_SIZE(HEADER(previousBlock));
    nextBlock = NEXT_BLOCK(ptr);
    mergedSize += GET_SIZE(HEADER(nextBlock));

    deleteBlock(nextBlock);
    deleteBlock(previousBlock);
    insertFreeBlock(previousBlock, mergedSize);
    ptr = previousBlock;
  }

  checkAll();
  return ptr;
}

/* Tree helper functions implementations */

static void insertFreeBlock(void *ptr, size_t size) {
  /* Wrapper for recursive, real insert function */

  initTreeNode(ptr, size);

  /* Calculate tree to insert based on size */
  int treeIndex = findTreeIndex(size);
  void *tree = getTree(treeIndex);

  SET_PTR(tree, insertFreeBlock_(GET_PTR(tree), ptr));
}

static void *insertFreeBlock_(void *root, void *ptr) {
  /* real insert function */
  if (root == NULL) { return ptr; }

  void *left = LEFT_CHILD(root);
  void *right = RIGHT_CHILD(root);

  if (ptr < root) {
    SET_PTR(left, insertFreeBlock_(GET_PTR(left), ptr));
  } else if (ptr > root) {
    SET_PTR(right, insertFreeBlock_(GET_PTR(right), ptr));
  } else {
    // must not happen
    fprintf(stderr, "Duplicate insertion in tree\n");
    exit(1);
  }

  updateHeight(root);
  root = makeBalance(root);
  return root;
}

static void *findFreeBlock(size_t targetSize) {
  /*
   * Find free block to allocate
   * free block's size should be >= targetSize
   * this is wrapper of real find function
   */
  int treeIndex = findTreeIndex(targetSize);

  void *allocateBlock = NULL;

  for (int i = treeIndex; i < NUM_TREE; i++) {
    // start to find from treeIndex
    void *tree = getTree(i);

    findFreeBlock_(GET_PTR(tree), targetSize, &allocateBlock);
    if (allocateBlock != NULL) {
      /* found! */
      break;
    }
  }

  if (allocateBlock == NULL) {
    return allocateBlock;
  } else {
    return splitAndPlace(allocateBlock, targetSize);
  }
}

static void findFreeBlock_(void *root,
                           size_t targetSize,
                           void **allocateBlock) {
  /* search by inOrder, best fit */
  if (root == NULL) return;

  size_t size = GET_SIZE(HEADER(root));
  void *left = GET_PTR(LEFT_CHILD(root));
  void *right = GET_PTR(RIGHT_CHILD(root));

  findFreeBlock_(left, targetSize, allocateBlock);

  if (size >= targetSize) {
    if (*allocateBlock == NULL) {
      *allocateBlock = root;
    } else if ((GET_SIZE(HEADER(*allocateBlock)) - targetSize) >
               (size - targetSize)) {
      *allocateBlock = root;
    }
  }

  findFreeBlock_(right, targetSize, allocateBlock);
}

static void *reallocSplitAndPlace(void *new_ptr,
                                  size_t targetSize,
                                  size_t oldSize) {
  /*
   * SplitAndPlace for realloc case (add memmove)
   * Invariants
   *	- new_ptr is not in segregated Tree
   *	- from new_ptr, oldSize ranges always have old_ptr's data (must copy)
   */

  void *allocateBlock = NULL;
  size_t newBlockSize = GET_SIZE(HEADER(new_ptr));
  if (targetSize < oldSize) oldSize = targetSize;
  size_t truncatedSize = newBlockSize - targetSize;
  int allocatePosition =
      defindeAllocateSplitPosition(newBlockSize, targetSize);

  if (allocatePosition == ALLOCATE_FROM_BACK) {
    // allocate from the end
    // assign header first is one of trick to calculate next block
    PUT(HEADER(new_ptr), PACK(truncatedSize, 0));
    allocateBlock = NEXT_BLOCK(new_ptr);

    // it can be overlapped, so use memmove instead of memcpy
    memmove(allocateBlock, new_ptr, oldSize);

    PUT(HEADER(allocateBlock), PACK(targetSize, 1));
    PUT(FOOTER(allocateBlock), PACK(targetSize, 1));
    insertFreeBlock(new_ptr, truncatedSize);
  } else if (allocatePosition == ALLOCATE_FROM_FRONT) {
    // allocate from the front
    // no need to memmove
    allocateBlock = new_ptr;
    PUT(HEADER(allocateBlock), PACK(targetSize, 1));
    PUT(FOOTER(allocateBlock), PACK(targetSize, 1));
    insertFreeBlock(NEXT_BLOCK(allocateBlock), truncatedSize);
  } else {
    allocateBlock = new_ptr;
    PUT(HEADER(allocateBlock), PACK(newBlockSize, 1));
    PUT(FOOTER(allocateBlock), PACK(newBlockSize, 1));
  }

  return allocateBlock;
}

static void *splitAndPlace(void *ptr, size_t targetSize) {
  /* Split ptr into targetSize allocated Block */

  void *allocateBlock = NULL;
  size_t ptrSize = GET_SIZE(HEADER(ptr));

  deleteBlock(ptr);
  int allocatePosition = defindeAllocateSplitPosition(ptrSize, targetSize);
  size_t truncatedSize = ptrSize - targetSize;
  if (allocatePosition == ALLOCATE_FROM_BACK) {
    insertFreeBlock(ptr, truncatedSize);
    allocateBlock = NEXT_BLOCK(ptr);
    PUT(HEADER(allocateBlock), PACK(targetSize, 1));
    PUT(FOOTER(allocateBlock), PACK(targetSize, 1));
  } else if (allocatePosition == ALLOCATE_FROM_FRONT) {
    allocateBlock = ptr;
    PUT(HEADER(allocateBlock), PACK(targetSize, 1));
    PUT(FOOTER(allocateBlock), PACK(targetSize, 1));
    insertFreeBlock(NEXT_BLOCK(allocateBlock), truncatedSize);
  } else {
    // allocate whole
    allocateBlock = ptr;
    PUT(HEADER(allocateBlock), PACK(ptrSize, 1));
    PUT(FOOTER(allocateBlock), PACK(ptrSize, 1));
  }

  return allocateBlock;
}

static void deleteBlock(void *ptr) {
  /* Delete Block Wrapper */
  size_t size = GET_SIZE(HEADER(ptr));
  int treeIndex = findTreeIndex(size);
  void *tree = getTree(treeIndex);

  SET_PTR(tree, deleteBlock_(GET_PTR(tree), ptr));
}

static void *deleteBlock_(void *root, void *ptr) {
  /* Delete ptr from target tree */
  if (root == NULL) return root;

  void *left = LEFT_CHILD(root);
  void *right = RIGHT_CHILD(root);
  void *leftChildAddress = GET_PTR(left);
  void *rightChildAddress = GET_PTR(right);

  if (ptr < root) {
    SET_PTR(left, deleteBlock_(leftChildAddress, ptr));
  } else if (ptr > root) {
    SET_PTR(right, deleteBlock_(rightChildAddress, ptr));
  } else {
    if (leftChildAddress == NULL && rightChildAddress == NULL) {
      return NULL;
    } else if (leftChildAddress == NULL && rightChildAddress != NULL) {
      root = rightChildAddress;
    } else if (leftChildAddress != NULL && rightChildAddress == NULL) {
      root = leftChildAddress;
    } else {
      void *smallest = getSmallestBlock(GET_PTR(right));

      /* copy other fields of root to smallest */
      SET_PTR(right, deleteBlock_(GET_PTR(right), smallest));
      root = smallest;
      SET_PTR(RIGHT_CHILD(root), GET_PTR(right));
      SET_PTR(LEFT_CHILD(root), GET_PTR(left));
    }
  }

  updateHeight(root);
  root = makeBalance(root);

  return root;
}

/* Helper functions for heap checker or debuggind*/
static void printTree() {
  // Print All tree's information (Wrapper)
  size_t size = MINIMUM_BLOCK_SIZE;
  for (int i = 0; i < NUM_TREE; i++) {
    void *tree = getTree(i);
    printf("Tree Num = %d, Size from %zu to %zu\n", i, size, size * 2);
    printTree_(GET_PTR(tree), 0);
    printf("\n");
    size *= 2;
  }
}
static void printTree_(void *root, unsigned int indent) {
  // print all tree's informationi
  if (root == NULL) { return; }
  printTree_(GET_PTR(LEFT_CHILD(root)), indent + 1);

  for (unsigned int i = 0; i < indent; i++) { printf("\t"); }
  printf("%p,%u, l=%p, r=%p\n",
         root,
         GET_SIZE(HEADER(root)),
         GET_PTR(LEFT_CHILD(root)),
         GET_PTR(RIGHT_CHILD(root)));

  printTree_(GET_PTR(RIGHT_CHILD(root)), indent + 1);
}

static void checkAllFreeBlocksInTree() {
  // check all free blocks are in tree
  void *traverse = heap_listp;

  while (GET_SIZE(HEADER(traverse)) != 0) {
    if (GET_ALLOC(HEADER(traverse)) == 0) {
      // free block
      size_t size = GET_SIZE(HEADER(traverse));
      int treeIndex = findTreeIndex(size);
      checkAllFreeBlocksInTree_(GET_PTR(getTree(treeIndex)), traverse);
      if (checker == 0) {
        printBlockInfo(traverse);
        fprintf(stderr, "is Free block, but not found in tree!\n");
        exit(NOT_ALL_FREE_BLOCKS_IN_TREE);
      }
    }

    traverse = NEXT_BLOCK(traverse);
  }
}

static void checkAllFreeBlocksInTree_(void *root, void *ptr) {
  if (root == NULL) return;

  if (ptr < root) {
    checkAllFreeBlocksInTree_(GET_PTR(LEFT_CHILD(root)), ptr);
  } else if (ptr > root) {
    checkAllFreeBlocksInTree_(GET_PTR(RIGHT_CHILD(root)), ptr);
  } else {
    checker = 1;
    return;
  }
}

static void checkAllTreesBalanced() {
  // check whether it is valid avl_tree
  for (int i = 0; i < NUM_TREE; i++) {
    void *tree = getTree(i);
    checkAllTreesBalanced_(GET_PTR(tree));
    if (checker == 0) {
      fprintf(stderr, "%d-th tree is unbalanced!\n", i);
      exit(NOT_ALL_TREES_ARE_BALANCED);
    }
  }
}

static void checkAllTreesBalanced_(void *root) {
  if (root == NULL) { return; }

  void *left = GET_PTR(LEFT_CHILD(root));
  void *right = GET_PTR(RIGHT_CHILD(root));
  checkAllTreesBalanced_(left);

  int leftHeight = (int) GET_HEIGHT(left);
  int rightHeight = (int) GET_HEIGHT(right);

  if ((-1 <= leftHeight - rightHeight && leftHeight - rightHeight <= 1) == 0) {
    checker = 0;
    return;
  }

  checkAllTreesBalanced_(right);
}

static void checkAllTreesOrderedByAddress() {
  // check whether all tree nodes are sorted by address
  for (int i = 0; i < NUM_TREE; i++) {
    void *tree = getTree(i);
    checkAllTreesOrderedByAddress_(GET_PTR(tree), NULL);
    if (checker == 0) {
      fprintf(stderr, "%d-th tree is not ordered by address!\n", i);
      exit(NOT_ALL_FREE_BLOCKS_SORTED_BY_ADDRESS);
    }
  }
}

static void checkAllTreesOrderedByAddress_(void *root, void *previous) {
  if (root == NULL) { return; }

  void *left = GET_PTR(LEFT_CHILD(root));
  void *right = GET_PTR(RIGHT_CHILD(root));

  checkAllTreesOrderedByAddress_(left, previous);

  if (previous == NULL) {
    previous = root;
  } else {
    if (previous > root) { checker = 0; }
  }

  checkAllTreesOrderedByAddress_(right, previous);
}

static void checkNoPossibleCoalesceBlocks() {
  return;
  void *traverse = heap_listp;
  int allocated;
  size_t size;

  void *prevBlock;
  void *nextBlock;

  while ((size = GET_SIZE(HEADER(traverse))) != 0) {
    allocated = GET_ALLOC(HEADER(traverse));
    prevBlock = PREV_BLOCK(traverse);
    nextBlock = NEXT_BLOCK(traverse);

    if (!allocated) {
      if (!GET_ALLOC(prevBlock)) {
        fprintf(stderr, "prevBlock not coalesced!\n");
        exit(NOT_COALESCED_BLOCK_EXIST);
      }

      if (!GET_ALLOC(nextBlock)) {
        fprintf(stderr, "nextBlock not coalesced!\n");
        exit(NOT_COALESCED_BLOCK_EXIST);
      }
    }

    traverse = NEXT_BLOCK(traverse);
  }
}

static void checkEveryFreeBlockMarkedAsFree() {
  for (int i = 0; i < NUM_TREE; i++) {
    void *tree = getTree(i);
    checkEveryFreeBlockMarkedAsFree_(GET_PTR(tree));
    if (checker == 0) {
      fprintf(
          stderr, "%d-th tree has free block whose allocate flag is 1!\n", i);
      exit(NOT_ALL_FREE_BLOCK_MARKED_AS_FREE);
    }
  }
}

static void checkEveryFreeBlockMarkedAsFree_(void *root) {
  if (root == NULL) return;

  void *left = GET_PTR(LEFT_CHILD(root));
  void *right = GET_PTR(RIGHT_CHILD(root));

  checkEveryFreeBlockMarkedAsFree_(left);

  if (GET_ALLOC(HEADER(root)) == 1) {
    checker = 0;
    return;
  }

  checkEveryFreeBlockMarkedAsFree_(right);
}

static void checkEveryTreeNodeInProperTree() {
  size_t size = MINIMUM_BLOCK_SIZE;

  for (int i = 0; i < NUM_TREE; i++) {
    void *tree = getTree(i);

    checkEveryTreeNodeInProperTree_(GET_PTR(tree), size, size * 2);
    if (checker == 0) {
      fprintf(stderr,
              "%d-th tree, with size range %zu to %zu has node whose size is "
              "not fit in range\n",
              i,
              size,
              size * 2);
      exit(NOT_ALL_TREE_NODE_IN_PROPER_TREE);
    }

    size *= 2;
  }
}

static void checkEveryTreeNodeInProperTree_(void *root,
                                            size_t minSize,
                                            size_t maxSize) {
  if (root == NULL) return;
  void *left = GET_PTR(LEFT_CHILD(root));
  void *right = GET_PTR(RIGHT_CHILD(root));

  checkEveryTreeNodeInProperTree_(left, minSize, maxSize);

  size_t size = GET_SIZE(HEADER(root));

  if (size < minSize || size >= maxSize) {
    checker = 0;
    return;
  }

  checkEveryTreeNodeInProperTree_(right, minSize, maxSize);
}

static void checkEveryBlocksBiggerThanMIN_BLOCK_SIZE() {
  void *traverse = heap_listp;
  size_t size;

  while ((size = GET_SIZE(HEADER(traverse))) != 0 && size != 8) {
    if (size < MINIMUM_BLOCK_SIZE) {
      fprintf(stderr,
              "Block whose size is smaller than MINIMUM_BLOCK_SIZE = %d "
              "found!\n",
              MINIMUM_BLOCK_SIZE);
      exit(NOT_ALL_BLOCKS_BIGGER_THAN_MIN_BLOCK_SIZE);
    }
    traverse = NEXT_BLOCK(traverse);
  }
}
