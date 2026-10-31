-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_theorem2
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.theorem2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:52:04.078251+00:00
-- url     : https://prove2.me/theorems/bd79af50-cd65-471c-b982-f7aac7bf0e3e
-- title:
--   Intrinsic steerability is a convex steering monotone
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. Let a deterministic one-way LOCC instrument have branches $\mathcal K_z$, let $q(x\mid x_f,z)$ and $r(a_f\mid x_f,x,a,z)$ be arbitrary classical channels, and set $p(z)=\operatorname{Tr}\mathcal K_z(\rho_B)$. For $p(z)>0$, define
--
--   $$\hat\rho_{B_f,z}^{a_f,x_f}=\frac1{p(z)}\sum_{a,x}r(a_f\mid x_f,x,a,z)q(x\mid x_f,z)\mathcal K_z(\hat\rho_B^{a,x}).$$
--
--   Intrinsic steerability satisfies all three properties:
--
--   $$\sum_{z:p(z)>0}p(z)S(\hat\rho_z)\le S(\hat\rho),\qquad \hat\rho\in\mathrm{LHS}\Longrightarrow S(\hat\rho)=0,$$
--   $$S(\lambda\hat\rho+(1-\lambda)\hat\sigma)\le\lambda S(\hat\rho)+(1-\lambda)S(\hat\sigma)\quad(0\le\lambda\le1).$$
--
--   Here $\hat\sigma$ is any assemblage on the same alphabets and Bob space, and LHS means a shared classical-variable decomposition with normalized Bob states. These properties make $S$ a convex steering monotone.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 3, Theorem 2

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

/-- Theorem 2, PDF p.3, proved on pp.7--10: all three convex-monotone clauses. -/
theorem theorem2 :
    IntrinsicAverageMonotonicity ∧ IntrinsicLHSVanishing ∧ IntrinsicConvexity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
