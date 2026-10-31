-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition14
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:58:16.781894+00:00
-- url     : https://prove2.me/theorems/74d27bc4-16f1-4d9c-873f-a1088047e06d
-- title:
--   Restricted intrinsic steerability is convex
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Let $\hat\rho$ and $\hat\sigma$ be assemblages on the same alphabets and Bob space, let $0\le\lambda\le1$, and construct $\hat\tau^{a,x}=\lambda\hat\rho^{a,x}+(1-\lambda)\hat\sigma^{a,x}$. Then
--
--   $$S^R(\hat\tau)\le\lambda S^R(\hat\rho)+(1-\lambda)S^R(\hat\sigma).$$
--
--   Both endpoints are included. This states convexity of the actual optimized functional on the computed mixture.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 13, Proposition 14

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

/-- Proposition 14, PDF p.13, (160)--(161): both convex-mixture endpoints. -/
theorem proposition14 : RestrictedConvexity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
