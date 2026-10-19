-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_two_moment_unit_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P19.two_moment_unit_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:54:36.994107+00:00
-- url     : https://prove2.me/theorems/16ed2d2a-5e90-45be-b0ee-ebc413785eb2
-- title:
--   Corollary 5.6
-- statement:
--   For $1/2\le r_1\le1$ and $0\le r_2\le r_1^2$,
--   $$\alpha(r_1,r_2)\le1\quad\Longleftrightarrow\quad2r_2-r_1^2\ge2r_1-1.$$
--   The extended value includes the infeasible $r_2=0$ case. This describes the first arc of the exact discrete boundary.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 31, Corollary 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Corollary 5.6; arXiv:2609.29471v1, PDF pp.31. -/
theorem two_moment_unit_bound (r1 r2 : ℝ) (hlo : 1/2≤r1) (hhi : r1≤1) (h2 : 0≤r2)
    (hupper : r2≤r1^2) :
    alpha ![r1,r2] ≤ 1 ↔ 2*r2-r1^2 ≥ 2*r1-1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
