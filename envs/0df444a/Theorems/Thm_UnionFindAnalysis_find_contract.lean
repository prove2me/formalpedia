-- Prove2me | Theorems.Thm_UnionFindAnalysis_find_contract
-- name    : UnionFindAnalysis.find_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:54:15.758102+00:00
-- url     : https://prove2.me/theorems/8c16ff9d-a8f1-4af4-bfc6-abae7245efaf
-- title:
--   Union-find: exact mutable find and full-compression contract
-- statement:
--   For a represented object and an in-range vertex $v$, a terminating `UnionFind.find.Call` returns the initial model's representative of $v$ and rewrites every parent pointer on the visited path to that root. The theorem provides a finite path witness of length $p$, the matching compressed model, and the same final heap's representation and storage effect. Only the parent array may change.
--
--   Its exact increment function `findCosts p` is $p+1$ on `uf_find`, $p$ on `uf_compress` and zero on every other clock. This is the operational foundation for the inverse-Ackermann bound, not a supplied runtime assumption.
--
--   The precondition `Rep heap layout model` connects an allocated object and distinct allocated parent/rank arrays to a valid forest on `Fin n`. Validity includes representative consistency, strictly increasing rank along nonroot parent links, and the root-mass rank bound. It does not assume a particular operation history. Vertex arguments belong to `Fin n`; no such argument exists when $n=0$.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean#L518-L536

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.find_contract :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (vertex : Fin n),
          Exists.{1} fun length =>
            Exists.{1} fun after =>
              Algo2Lean.UnionFind.Find model vertex (model.representative vertex) length ∧
                Algo.union_find.UnionFind.find.Call heap
                    (Prod.mk.{0, 0} layout.object (↑(↑vertex : Nat) : Int)) after
                    (↑(↑(model.representative vertex) : Nat) : Int) ∧
                  UnionFindAnalysis.Rep after layout
                      (UnionFindAnalysis.findResult model vertex length) ∧
                    UnionFindAnalysis.Storage heap after (List.cons.{0} layout.parent List.nil.{0}) ∧
                      heap.Increments after (UnionFindAnalysis.findCosts length) := by
  sorry
