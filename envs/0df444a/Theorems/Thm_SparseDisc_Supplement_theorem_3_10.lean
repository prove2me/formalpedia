-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_3_10
-- name    : SparseDisc.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:11:52.834325+00:00
-- url     : https://prove2.me/theorems/cb2db581-aedd-4547-be4e-fdf5e634a918
-- title:
--   Theorem 3.10 — six-function bound and $K_5,K_6,K_8$
-- statement:
--   The computer-assisted exact-arithmetic calculation proves that every finite $2$-sparse instance with at most six functions has discrepancy at most $2$. It also establishes
--   $$
--   K_5=3,\qquad K_6=4,\qquad K_8\ge5.
--   $$
--
--   Differences from the source:
--   - encoding: instances with at most six functions → an arbitrary finite function type whose cardinality is at most six, with the published instance and declared-support predicates; reason: Lean convention, preserving supports that may contain irrelevant coordinates
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 3.10, p.18

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_K

namespace SparseDisc.Supplement

/-- **Theorem 3.10** (computer-assisted; Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.18).
Every 2-sparse instance with at most six functions has discrepancy at most `2`; moreover
`K₅ = 3`, `K₆ = 4`, and `K₈ ≥ 5`. -/
theorem theorem_3_10 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (g : V → SparseDisc.Cube ι → ℝ) (U : V → Finset ι),
      Fintype.card V ≤ 6 → SparseDisc.IsInstance g U →
      SparseDisc.IsTwoSparseSupp U → SparseDisc.InstDiscLE g 2) ∧
    K 5 = 3 ∧ K 6 = 4 ∧ 5 ≤ K 8 := by sorry

end SparseDisc.Supplement
