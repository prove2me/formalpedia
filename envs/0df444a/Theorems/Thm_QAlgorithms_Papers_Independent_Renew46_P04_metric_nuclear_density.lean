-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_nuclear_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_nuclear_density
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:11:28.193534+00:00
-- url     : https://prove2.me/theorems/b260eb30-ad66-43e6-9f4d-6e3e93c909b4
-- title:
--   Corollary 4.9(a,b): metric π-property gives nuclear density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $X^*$ has the metric $\pi$ property. Each condition (a) $Y$ has metric $\pi$, or (b) $Y$ is uniformly convex, implies
--
--   $$
--   \overline{\mathrm{NA}_{\mathcal N}(X,Y)}^{\|\cdot\|_N}=\mathcal N(X,Y).
--   $$
--
--   The domain assumption concerns $X^*$; no approximation-property or tensor-identification consequence is added as an assumption.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 16, Corollary 4.9(a,b): metric π-property gives nuclear density

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

/-- PDF p.16, Corollary 4.9(a,b): the domain assumption is on X*, not X. -/
theorem metric_nuclear_density (hX : MetricPi K (X →L[K] K)) :
    (MetricPi K Y → NuclearDense K X Y) ∧
    (UniformConvexSpace Y → NuclearDense K X Y) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
