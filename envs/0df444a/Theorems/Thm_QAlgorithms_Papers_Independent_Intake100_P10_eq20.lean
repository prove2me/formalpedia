-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_eq20
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.eq20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:03:50.494596+00:00
-- url     : https://prove2.me/theorems/e88a0483-e4c4-4e3c-9c74-f86b0f309e61
-- title:
--   Intrinsic dominates restricted intrinsic steerability
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Then
--
--   $$S(\hat\rho)\ge S^R(\hat\rho).$$
--
--   This compares the two distinct optimization problems; it does not identify them.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Equation (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Equation (20), PDF p.4: identity Bob strategy gives restricted <= intrinsic. -/
theorem eq20 {X A B : Type} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho : AssemblageCoefficients X A B) (hrho : IsAssemblage rho) :
    restrictedSteerability rho ≤ intrinsicSteerability rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
