-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_cqTensorSingleLetter
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.cqTensorSingleLetter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:25:25.026928+00:00
-- url     : https://prove2.me/theorems/2d9f0194-bd07-407f-8722-320562b222bd
-- title:
--   Iid cq single-letterization
-- statement:
--   Let $E$ be a finite classical–quantum ensemble, $n\ge1$ an integer, and $R\ge0$. Let $E^{\otimes n}$ be its iid product ensemble and define $D_n^*(E,R)=n^{-1}D^*(E^{\otimes n},nR)$. Then
--
--   $$D_n^*(E,R)=D^*(E,R).$$
--
--   The objective and communication constraint are both normalized per source copy. This equality removes any block advantage for the cq variational curve.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 7, §2, unnumbered after (8): iid single-letterization

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF p.7, unnumbered consequence of (8): iid single-letterization at positive blocklength. -/
theorem cqTensorSingleLetter (E : CQData X Q) (hE : E.Valid) (n : ℕ) (hn : 0 < n)
    (R : ℝ) (hR : 0 ≤ R) : dStarBlock E n R = dStar E R := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
