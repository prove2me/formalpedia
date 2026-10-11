-- Prove2me | Theorems.Thm_UnionFindAnalysis_constructor_rep
-- name    : UnionFindAnalysis.constructor_rep
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:46.388001+00:00
-- url     : https://prove2.me/theorems/96bbc71f-5f9e-45da-8f0e-0e5dfd0816e6
-- title:
--   Union-find: constructor establishes the singleton representation
-- statement:
--   For every heap and natural size $n$, `newHeap heap n` at `newLayout heap` represents `Algo2Lean.UnionFind.initial n`. Each vertex is its own parent and representative, every rank is zero and each root has unit ghost mass. The empty universe is included.
--
--   This connects the allocated mutable object to the pure initial forest and lets any subsequent find or union use the general method contracts. It is a representation theorem; the actual constructor call is proved separately.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find_init.lean#L281-L306

import Definitions.Def_Algo_union_find_init_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.constructor_rep :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      UnionFindAnalysis.Rep (UnionFindAnalysis.newHeap heap size) (UnionFindAnalysis.newLayout heap)
        (Algo2Lean.UnionFind.initial size) := by
  sorry
