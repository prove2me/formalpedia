-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_goldenThompsonEquality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.goldenThompsonEquality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:09:24.905198+00:00
-- url     : https://prove2.me/theorems/d566a50d-2d09-4143-bb80-85f943bdf279
-- title:
--   Section 4, printed 3.1: Golden–Thompson inequality and equality criterion
-- statement:
--   For arbitrary self-adjoint matrices $A,B$ on a finite complex Hilbert space,
--
--   $$\operatorname{Tr}e^{A+B}\le\operatorname{Tr}(e^Ae^B),\qquad
--   \operatorname{Tr}e^{A+B}=\operatorname{Tr}(e^Ae^B)\iff AB=BA.$$
--
--   The Lean traces take real parts, which does not change these real quantities. No density or commutativity hypothesis is added.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 6, Section 4, printed 3.1: Golden–Thompson inequality and equality criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.6, printed subsection 3.1.
Both the Golden--Thompson inequality and its equality iff are retained.
The finite-dimensional self-adjoint matrices need not be densities. -/
theorem goldenThompsonEquality {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace.re ≤
      (NormedSpace.exp A * NormedSpace.exp B).trace.re ∧
    ((NormedSpace.exp (A + B)).trace.re =
      (NormedSpace.exp A * NormedSpace.exp B).trace.re ↔ Commute A B) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
