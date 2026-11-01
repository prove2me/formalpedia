-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_cat_sweetSpot
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.cat_sweetSpot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:27:02.428334+00:00
-- url     : https://prove2.me/theorems/db3a028f-05de-4c13-ab08-912e4fa6c954
-- title:
--   Leading-order single-loss cat sweet spot
-- statement:
--   Consider the $S=1$ projected-coherent cat states $|0_a\rangle,|1_a\rangle$ with real $a>0$. Their mean photon numbers are finite. Equality of their mean photon numbers, which is the leading-order no-loss backaction condition, is equivalent to
--
--   $$\langle0_a|\hat n|0_a\rangle=\langle1_a|\hat n|1_a\rangle\quad\Longleftrightarrow\quad \sin(a^2)\cosh(a^2)+\cos(a^2)\sinh(a^2)=0.$$
--
--   This is the pole-free form of $\tan(a^2)=-\tanh(a^2)$. It does not assert exact finite-loss correction, nor treat the approximate numerical root as an exact constant.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 10, §V A (5.9)–(5.10): leading-order single-loss cat sweet spot

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.10 (5.9)--(5.10): exact leading-order condition, cross-multiplied to
avoid turning tangent poles into solutions. Rounded numerical roots are not equalities. -/
theorem cat_sweetSpot (a : ℝ) (ha : 0 < a) :
    (fockMomentDomain (catCodeCoordinates a 1 0) 1 ∧ fockMomentDomain (catCodeCoordinates a 1 1) 1) ∧
    (numberMoment (catCodeCoordinates a 1 0) 1 = numberMoment (catCodeCoordinates a 1 1) 1 ↔
      Real.sin (a ^ 2) * Real.cosh (a ^ 2) +
        Real.cos (a ^ 2) * Real.sinh (a ^ 2) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
