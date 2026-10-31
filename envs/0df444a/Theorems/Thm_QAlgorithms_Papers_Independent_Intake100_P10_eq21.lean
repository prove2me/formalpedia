-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_eq21
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.eq21
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:04:35.371689+00:00
-- url     : https://prove2.me/theorems/8c414142-adc5-4d37-9cdf-afe227f79e30
-- title:
--   Intrinsic steerability is bounded by the outcome alphabet
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Then
--
--   $$0\le S(\hat\rho)\le\log_2|A|.$$
--
--   The dimension is the cardinality of the classical output alphabet, not the number of inputs or Bob’s Hilbert dimension. This also guarantees that intrinsic steerability is finite.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Equation (21)

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

/-- Equation (21), PDF p.4: the output alphabet A gives the finite upper bound.
The ENNReal formulation includes nonnegativity and excludes infinity by the bound. -/
theorem eq21 {X A B : Type} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho : AssemblageCoefficients X A B) (hrho : IsAssemblage rho) :
    0 ≤ intrinsicSteerability rho ∧
      intrinsicSteerability rho ≤ ENNReal.ofReal (Real.logb 2 (Fintype.card A)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
