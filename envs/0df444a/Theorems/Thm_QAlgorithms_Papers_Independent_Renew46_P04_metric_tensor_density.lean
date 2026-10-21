-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_tensor_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_tensor_density
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:10:58.345639+00:00
-- url     : https://prove2.me/theorems/a7b4c1b4-bb4d-4207-9eb0-0327bc28f119
-- title:
--   Theorem 4.8(a,b): metric π-property gives tensor density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $X$ has the metric $\pi$ property. Each of the following conditions on $Y$ implies the displayed density: (a) $Y$ has the metric $\pi$ property; (b) $Y$ is uniformly convex.
--
--   $$
--   \overline{\mathrm{NA}_\pi(P(X,Y))}^{\|\cdot\|_\pi}=P(X,Y).
--   $$
--
--   Both alternatives are included and use the same contractive-complementation definition.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 15, Theorem 4.8(a,b): metric π-property gives tensor density

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- PDF pp.15–16, Theorem 4.8(a,b): both alternatives give density, not universal attainment. -/
theorem metric_tensor_density (hX : MetricPi K X) :
    (MetricPi K Y → TensorDense K X Y) ∧
    (UniformConvexSpace Y → TensorDense K X Y) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
