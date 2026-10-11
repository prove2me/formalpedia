-- Prove2me | Theorems.Thm_SortIndicesAnalysis_call
-- name    : SortIndicesAnalysis.call
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:38.587071+00:00
-- url     : https://prove2.me/theorems/67476c98-cb75-466b-bdf8-6eb449ba7184
-- title:
--   Indexed-heap sorting: correctness and logarithmic running time
-- statement:
--   For an allocated key sequence and a nonnegative count $m$, a terminating `sort_indices.Call` returns a fresh valid sequence whose first $m$ entries permute $0,\ldots,m-1$ and are ordered by their original keys. Negative or duplicate integer keys and $m=0$ are allowed; stability among equal keys is not asserted. The sorting postcondition does not constrain indices outside this prefix.
--
--   Every previously allocated caller sequence and object, and all collections, are preserved. `Budget m (2m)` bounds each clock increment by $2m$ times its rate: 1 for `sort_steps`, $2\lfloor\log_2(m+1)\rfloor$ for `heap_comparisons`, and $\lfloor\log_2(m+1)\rfloor+1$ for `heap_swaps`. Consequently their sum is at most
--   $$
--   2m\bigl(3\lfloor\log_2(m+1)\rfloor+2\bigr).
--   $$
--   Clients reuse this call contract to obtain ordered identifiers, preservation and costs together. The implementation repeatedly inserts and extracts from an indexed min-priority queue; it is not the exact in-place HEAPSORT program of CLRS §6.4. Its heap structure and operations correspond to fourth-edition Chapter 6, especially §6.5.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   ## Algorithm source
--
--   Project import root: `examples/kruskal`. Entry file: `sort_indices.algo`.
--
--   ### `indexed_heap.algo`
--
--   ```python
--   # An indexed binary min-heap for Dijkstra's priority queue.
--   # vertices[position] and positions[vertex] are inverse on the active prefix.
--   # keys is indexed by vertex; position -1 means the vertex is not in the heap.
--   # Clients use nonnegative vertex identifiers, so pop_min can use -1 for empty.
--
--   class MinHeap:
--       vertices: Seq
--       positions: Seq
--       keys: Seq
--       size: Int
--
--       def __init__(self) -> None:
--           self.vertices = const(0)
--           self.positions = const(-1)
--           self.keys = const(0)
--           self.size = 0
--
--       def swap(self, i: Int, j: Int) -> None:
--           a = self.vertices[i]
--           b = self.vertices[j]
--           # @exchange
--           self.vertices[i] = b
--           self.vertices[j] = a
--           self.positions[a] = j
--           self.positions[b] = i
--           tick("heap_swaps")
--
--       def sift_up(self, i: Int) -> None:
--           # @up_loop
--           while i > 0:
--               parent = (i - 1) // 2
--               tick("heap_comparisons")
--               if self.keys[self.vertices[parent]] <= self.keys[self.vertices[i]]:
--                   return
--               self.swap(i, parent)
--               i = parent
--
--       def sift_down(self, i: Int) -> None:
--           # @down_loop
--           while 2 * i + 1 < self.size:
--               child = 2 * i + 1
--               right = child + 1
--               if right < self.size:
--                   tick("heap_comparisons")
--                   if self.keys[self.vertices[right]] < self.keys[self.vertices[child]]:
--                       child = right
--               # @compare_child
--               tick("heap_comparisons")
--               if self.keys[self.vertices[i]] <= self.keys[self.vertices[child]]:
--                   return
--               self.swap(i, child)
--               i = child
--
--       def push_or_decrease(self, vertex: Int, key: Int) -> None:
--           i = self.positions[vertex]
--           if i < 0:
--               self.keys[vertex] = key
--               i = self.size
--               self.vertices[i] = vertex
--               self.positions[vertex] = i
--               self.size += 1
--               self.sift_up(i)
--           else:
--               tick("heap_comparisons")
--               if key < self.keys[vertex]:
--                   self.keys[vertex] = key
--                   self.sift_up(i)
--
--       def pop_min(self) -> Int:
--           if self.size <= 0:
--               return -1
--           vertex = self.vertices[0]
--           last = self.size - 1
--           self.swap(0, last)
--           self.size = last
--           self.positions[vertex] = -1
--           if last > 0:
--               self.sift_down(0)
--           return vertex
--
--       def is_empty(self) -> Bool:
--           return self.size <= 0
--   ```
--
--   ### `sort_indices.algo`
--
--   ```python
--   # Order the identifiers [0, count) by their keys using a reusable binary heap.
--   # This supplies Kruskal's sort-by-weight step: insert every identifier, then
--   # extract minima. It is not the in-place HEAPSORT procedure from CLRS Chapter 6.
--   # Only identifiers are reordered; keys are unchanged. Equal-key identifiers
--   # may appear in either order.
--   from indexed_heap import MinHeap
--
--
--   def sort_indices(keys: Seq, count: Int) -> Seq:
--       queue = MinHeap()
--       result = const(0)
--       index = 0
--       # @insert
--       while index < count:
--           tick("sort_steps")
--           queue.push_or_decrease(index, keys[index])
--           index += 1
--       index = 0
--       # @extract
--       while index < count:
--           tick("sort_steps")
--           result[index] = queue.pop_min()
--           index += 1
--       return result
--   ```
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/sort_indices.lean#L448-L522

import Definitions.Def_Algo_sort_indices_Analysis
import Theorems.Thm_BinaryModuleAnalysis_insert_correct
import Theorems.Thm_BinaryModuleAnalysis_pop_singleton_correct
import Theorems.Thm_BinaryModuleAnalysis_pop_multiple_correct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem SortIndicesAnalysis.call :
    ∀ (heap : Algo2LeanGenerated.Heap) (keys : Algo2LeanGenerated.SeqRef) (count : Int),
      LT.lt.{0} keys heap.nextRef →
        LE.le.{0} (0 : Int) count →
          Exists.{1} fun after =>
            Exists.{1} fun result =>
              Algo.sort_indices.sort_indices.Call heap (Prod.mk.{0, 0} keys count) after result ∧
                SortIndicesAnalysis.SortedPermutation (heap.read keys) count (after.read result) ∧
                  SortIndicesAnalysis.Preserves heap after ∧
                    LE.le.{0} heap.nextRef result ∧
                      LT.lt.{0} result after.nextRef ∧
                        SortIndicesAnalysis.Budget count (HMul.hMul.{0, 0, 0} (2 : Nat) count.toNat)
                          heap after := by
  sorry
