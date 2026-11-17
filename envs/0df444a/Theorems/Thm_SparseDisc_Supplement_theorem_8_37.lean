-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_8_37
-- name    : SparseDisc.Supplement.theorem_8_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:15:26.495223+00:00
-- url     : https://prove2.me/theorems/ecf0d300-3728-4432-978b-005fb658f46a
-- title:
--   Theorem 8.37 — thin shared bundles for instances
-- statement:
--   Let $G$ be a finite instance with $n$ functions in which any two declared supports share at most $s$ items.
--
--   1. If $G$ is $2$-sparse, then
--      $$
--      \operatorname{disc}(G)\le1+2\left\lceil\sqrt{sn/2}\right\rceil.
--      $$
--      In particular, a simple item multigraph gives $\operatorname{disc}(G)\le1+2\lceil\sqrt{n/2}\rceil$.
--   2. If $G$ is $t$-sparse, then
--      $$
--      \operatorname{disc}(G)\le1+2s\sqrt{t(t-1)n}.
--      $$
--
--   Differences from the source:
--   - encoding: $n$ functions and at most $s$ shared items → `n` is the cardinality of a finite function type and every intersection of two distinct declared supports has cardinality at most `s`; reason: Lean convention, preserving nonminimal supports
--   - reading: simple item multigraph → pairwise declared-support intersections have cardinality at most one; reason: under 2-sparsity this is exactly absence of parallel non-private item edges
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.37, p.46

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_IsTSparseSupp
import Definitions.Def_SparseDisc_Supplement_PairwiseSharedCap

namespace SparseDisc.Supplement

/-- **Theorem 8.37** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.46). The instance-level pairwise shared-item
bounds are stated for both `t=2` and general `t`, including the simple-item-multigraph consequence. -/
theorem theorem_8_37 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (g : V → SparseDisc.Cube ι → ℝ) (U : V → Finset ι) (s : ℕ),
      SparseDisc.IsInstance g U → PairwiseSharedCap U s →
      SparseDisc.IsTwoSparseSupp U →
      SparseDisc.InstDiscLE g
        (1 + 2 * ((Nat.ceil (Real.sqrt (((s * Fintype.card V : ℕ) : ℝ) / 2)) : ℕ) : ℝ))) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (g : V → SparseDisc.Cube ι → ℝ) (U : V → Finset ι),
      SparseDisc.IsInstance g U → PairwiseSharedCap U 1 →
      SparseDisc.IsTwoSparseSupp U →
      SparseDisc.InstDiscLE g
        (1 + 2 * ((Nat.ceil (Real.sqrt ((Fintype.card V : ℝ) / 2)) : ℕ) : ℝ))) ∧
    (∀ (t s : ℕ), 1 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (g : V → SparseDisc.Cube ι → ℝ)
      (U : V → Finset ι), SparseDisc.IsInstance g U → PairwiseSharedCap U s →
      IsTSparseSupp t U → SparseDisc.InstDiscLE g
        (1 + 2 * s * Real.sqrt ((t * (t - 1) * Fintype.card V : ℕ) : ℝ))) := by sorry

end SparseDisc.Supplement
