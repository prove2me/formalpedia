-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition12
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:59:33.601899+00:00
-- url     : https://prove2.me/theorems/4d3c15da-e63e-40a7-ab5d-7a5c61d77a47
-- title:
--   Restricted intrinsic steerability vanishes on LHS assemblages
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Suppose there exist a discrete probability law $p_\Lambda$, normalized positive trace-class Bob states $\sigma_B^\lambda$, and conditional outcome laws $p(a\mid x,\lambda)$, with
--
--   $$\hat\rho_B^{a,x}=\sum_\lambda p_\Lambda(\lambda)p(a\mid x,\lambda)\sigma_B^\lambda.$$
--
--   Then
--
--   $$S^R(\hat\rho)=0.$$
--
--   This is the forward vanishing statement of this paper. It does not assert faithfulness in the reverse direction.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 12, Proposition 12

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

/-- Proposition 12, PDF p.12, (137)--(138): only LHS implies zero. -/
theorem proposition12 : RestrictedLHSVanishing := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
