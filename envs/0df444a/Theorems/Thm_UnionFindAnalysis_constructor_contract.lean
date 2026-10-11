-- Prove2me | Theorems.Thm_UnionFindAnalysis_constructor_contract
-- name    : UnionFindAnalysis.constructor_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:50.337837+00:00
-- url     : https://prove2.me/theorems/75986ca5-05f4-4a23-9362-774c68a27675
-- title:
--   Union-find: reusable constructor correctness and initialization running time
-- statement:
--   For any heap and natural size $n$, the constructor terminates with a fresh union-find object representing $n$ singleton components. It allocates exactly two sequence references and one object reference, allocates no typed collection, and preserves every previously allocated caller sequence, object and collection. It charges exactly $n+1$ `uf_init` ticks and zero ticks on all other clocks.
--
--   The final heap is `newHeap heap n`; its public representation is `newLayout heap` with pure model `initial n`, whose potential is zero. The case $n=0$ is valid. Later method calls use the returned representation without repeating initialization or resetting clocks.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find_init.lean#L395-L407

import Definitions.Def_Algo_union_find_init_Analysis
import Theorems.Thm_UnionFindAnalysis_constructor_summary
import Theorems.Thm_UnionFindAnalysis_constructor_rep

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.constructor_contract :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      Algo.union_find.UnionFind.Call heap (↑size : Int) (UnionFindAnalysis.newHeap heap size)
          heap.nextObject ∧
        UnionFindAnalysis.Rep (UnionFindAnalysis.newHeap heap size) (UnionFindAnalysis.newLayout heap)
            (Algo2Lean.UnionFind.initial size) ∧
          heap.Footprint (UnionFindAnalysis.newHeap heap size) List.nil.{0} List.nil.{0} List.nil.{0} ∧
            heap.Increments (UnionFindAnalysis.newHeap heap size)
                (UnionFindAnalysis.constructorCosts size) ∧
              Eq.{1} (UnionFindAnalysis.newHeap heap size).nextRef
                  (HAdd.hAdd.{0, 0, 0} heap.nextRef (2 : Nat)) ∧
                Eq.{1} (UnionFindAnalysis.newHeap heap size).nextObject
                    (HAdd.hAdd.{0, 0, 0} heap.nextObject (1 : Nat)) ∧
                  Eq.{1} (UnionFindAnalysis.newHeap heap size).nextCollection heap.nextCollection := by
  sorry
