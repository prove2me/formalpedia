-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_local_nuclear_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.local_nuclear_density
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:08:43.928977+00:00
-- url     : https://prove2.me/theorems/cc923256-cd43-416f-a8ee-d5ff4c278711
-- title:
--   Proposition 4.3: local bilinear property and nuclear density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Suppose $(X^*\times Y,\mathbb K)$ has the local $L_{o,o}$ property for bilinear forms: for each positive accuracy and fixed norm-one form, a positive almost-attainment threshold is chosen before the pair of unit vectors. Then
--
--   $$
--   \overline{\mathrm{NA}_{\mathcal N}(X,Y)}^{\|\cdot\|_N}=\mathcal N(X,Y).
--   $$
--
--   The fixed form is not perturbed in the local property, and density is measured in nuclear norm.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 12, Proposition 4.3: local bilinear property and nuclear density

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

/-- PDF p.12, Proposition 4.3: approximation is in the nuclear norm. -/
theorem local_nuclear_density (h : LocalBilinear K (X →L[K] K) Y) : NuclearDense K X Y := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
