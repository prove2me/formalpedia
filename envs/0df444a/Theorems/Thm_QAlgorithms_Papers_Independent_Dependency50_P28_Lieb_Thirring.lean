-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_Lieb_Thirring
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.Lieb_Thirring
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:05:46.591376+00:00
-- url     : https://prove2.me/theorems/371c3050-0ebf-4047-b09f-27141652eae1
-- title:
--   Lieb-Thirring trace inequality
-- statement:
--   For any positive semidefinite operators A and B on a finite-dimensional complex Hilbert space and any α>1,
--
--   $$
--   \operatorname{Tr}(ABA)^\alpha\leq\operatorname{Tr}A^\alpha B^\alpha A^\alpha.
--   $$
--
--   This is the trace-power inequality rederived from the operational exponent formula.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 17, Corollary IV.15 (Lieb-Thirring inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.17: Lieb-Thirring trace inequality. Equation (91) has TWO copies of A^alpha. No density normalization or support inclusion is imposed. The corollary explicitly refers to (91). -/
theorem Lieb_Thirring (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef) (alpha : ℝ) (ha : 1 < alpha) :
    tr (supportPower (A * B * A) alpha) ≤ tr (supportPower A alpha * supportPower B alpha * supportPower A alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
