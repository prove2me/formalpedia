-- Prove2me | Theorems.Thm_UnionFindAnalysis_constructor_summary
-- name    : UnionFindAnalysis.constructor_summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:48.626852+00:00
-- url     : https://prove2.me/theorems/5d3ed58c-eab8-430d-a34b-893412ef36c3
-- title:
--   Union-find: constructor execution for singleton components
-- statement:
--   For any starting heap and natural size $n$, `UnionFind.Call` terminates, returning the old `heap.nextObject` in the explicitly described `newHeap heap n`. The construction allocates the parent/rank arrays, stores the size and initializes each in-range parent to itself.
--
--   This is the operational component of `constructor_contract`. The representation, freshness, preservation and exact cost claims are supplied by its companion theorems rather than being additional premises of this execution statement.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find_init.lean#L210-L224

import Definitions.Def_Algo_union_find_init_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.constructor_summary :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      Algo.union_find.UnionFind.Call heap (↑size : Int) (UnionFindAnalysis.newHeap heap size)
        heap.nextObject := by
  sorry
