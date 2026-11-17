-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_3_8
-- name    : SparseDisc.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:11:16.010506+00:00
-- url     : https://prove2.me/theorems/dd3161dc-ed38-46b5-9c86-cb148eba57af
-- title:
--   Theorem 3.8 — $K_4$ and five-function 2-sparse bounds
-- statement:
--   The computer-assisted exact-arithmetic calculation proves
--   $$
--   K_4\le3.
--   $$
--   It also proves that every finite $2$-sparse instance with at most five functions has discrepancy at most $2$.
--
--   Differences from the source:
--   - encoding: instances with at most five functions → an arbitrary finite function type whose cardinality is at most five, with the published instance and declared-support predicates; reason: Lean convention, preserving supports that may contain irrelevant coordinates
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 3.8, p.17

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_Supplement_K

namespace SparseDisc.Supplement

/-- **Theorem 3.8** (computer-assisted; Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.17).
`K₄ ≤ 3`, and every 2-sparse instance with at most five functions has discrepancy at most `2`. -/
theorem theorem_3_8 :
    K 4 ≤ 3 ∧
    ∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (g : V → SparseDisc.Cube ι → ℝ) (U : V → Finset ι),
      Fintype.card V ≤ 5 → SparseDisc.IsInstance g U →
      SparseDisc.IsTwoSparseSupp U → SparseDisc.InstDiscLE g 2 := by sorry

end SparseDisc.Supplement
