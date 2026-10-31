-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition10
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:57:30.981671+00:00
-- url     : https://prove2.me/theorems/f010a961-3425-4e14-ace7-f499fee5bf94
-- title:
--   Intrinsic steerability is convex
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Let $\hat\rho$ and $\hat\sigma$ be assemblages on the same alphabets and Bob space, let $0\le\lambda\le1$, and construct $\hat\tau^{a,x}=\lambda\hat\rho^{a,x}+(1-\lambda)\hat\sigma^{a,x}$. Then
--
--   $$S(\hat\tau)\le\lambda S(\hat\rho)+(1-\lambda)S(\hat\sigma).$$
--
--   Both endpoints are included. This states convexity of the actual optimized functional on the computed mixture.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 9, Proposition 10

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

/-- Proposition 10, PDF pp.9--10, (99)--(119): constructed mixtures, including
lambda=0 and lambda=1. -/
theorem proposition10 : IntrinsicConvexity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
