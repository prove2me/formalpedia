-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_theorem4
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.theorem4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:52:48.119037+00:00
-- url     : https://prove2.me/theorems/7501be2c-50ca-4b2a-983d-12e5f03551db
-- title:
--   Restricted intrinsic steerability is a convex steering monotone
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. A restricted deterministic one-way LOCC operation has a Bob instrument $\{\mathcal K_z\}_z$, an input channel $q(x\mid x_f)$ independent of $z$, and output channel $r(a_f\mid a,x,x_f,z)$. Its output is
--
--   $$\hat\sigma_{B'}^{a_f,x_f}=\sum_{a,x,z}q(x\mid x_f)r(a_f\mid a,x,x_f,z)\mathcal K_z(\hat\rho_B^{a,x}).$$
--
--   Restricted intrinsic steerability satisfies
--
--   $$S^R(\hat\sigma)\le S^R(\hat\rho),\qquad \hat\rho\in\mathrm{LHS}\Longrightarrow S^R(\hat\rho)=0,$$
--   $$S^R(\lambda\hat\rho+(1-\lambda)\hat\tau)\le\lambda S^R(\hat\rho)+(1-\lambda)S^R(\hat\tau)\quad(0\le\lambda\le1),$$
--
--   for every assemblage $\hat\tau$ on the same spaces. These are deterministic monotonicity, LHS vanishing, and convexity. The output has its $z$ register discarded.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 4, Theorem 4

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

/-- Theorem 4, PDF p.4, proved on pp.12--13: deterministic restricted
monotonicity, LHS vanishing, and convexity. -/
theorem theorem4 :
    RestrictedDeterministicMonotonicity ∧ RestrictedLHSVanishing ∧ RestrictedConvexity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
