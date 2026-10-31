-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition7
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:55:36.040991+00:00
-- url     : https://prove2.me/theorems/440e7c85-2c4f-4cf1-8dcb-7fd7ad7db812
-- title:
--   Intrinsic steerability vanishes on LHS assemblages
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Suppose there exist a discrete probability law $p_\Lambda$, normalized positive trace-class Bob states $\sigma_B^\lambda$, and conditional outcome laws $p(a\mid x,\lambda)$, with
--
--   $$\hat\rho_B^{a,x}=\sum_\lambda p_\Lambda(\lambda)p(a\mid x,\lambda)\sigma_B^\lambda.$$
--
--   Then
--
--   $$S(\hat\rho)=0.$$
--
--   This is the vanishing property on local-hidden-state assemblages. No converse and no zero-CMI-extension premise is assumed.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 7, Proposition 7

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

/-- Proposition 7, PDF p.7, (71)--(72): LHS is the only extra premise. -/
theorem proposition7 : IntrinsicLHSVanishing := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
