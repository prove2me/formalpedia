-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_eq22
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.eq22
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:05:29.593136+00:00
-- url     : https://prove2.me/theorems/56236971-0c96-452a-b632-36f52ea23c05
-- title:
--   Restricted steerability dimension bound
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Suppose additionally that Bob’s Hilbert space has finite positive dimension $d_B$. Then
--
--   $$0\le S^R(\hat\rho)\le\min\{\log_2|A|,\log_2 d_B\}.$$
--
--   This is the finite-dimensional specialization of the source’s bound. It never interprets an infinite Hilbert dimension as a natural-valued finrank of zero.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Equation (22)

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

/-- Equation (22), PDF p.4: finite-dimensional Bob specialization. Nonempty B
excludes the impossible zero-dimensional normalized state; Nat finrank on an
infinite space is never used. A is the OUTCOME alphabet, not the input alphabet. -/
theorem eq22 {X A B : Type} [Fintype X] [Fintype A] [Fintype B]
    [Nonempty X] [Nonempty A] [Nonempty B]
    (rho : AssemblageCoefficients X A B) (hrho : IsAssemblage rho) :
    0 ≤ restrictedSteerability rho ∧ restrictedSteerability rho ≤
      ENNReal.ofReal (min (Real.logb 2 (Fintype.card A)) (Real.logb 2 (Fintype.card B))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
