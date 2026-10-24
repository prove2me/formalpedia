-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_local_tensor_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.local_tensor_density
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:09:39.908388+00:00
-- url     : https://prove2.me/theorems/b0a0bfb5-0a6e-441c-b42d-a818b622e034
-- title:
--   Proposition 4.5: local bilinear property and tensor density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $(X\times Y,\mathbb K)$ has the local $L_{o,o}$ property for bilinear forms, with threshold depending on the accuracy and fixed form before the almost-attaining pair, then
--
--   $$
--   \overline{\mathrm{NA}_\pi(P(X,Y))}^{\|\cdot\|_\pi}=P(X,Y).
--   $$
--
--   Approximation uses the completed projective norm.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 14, Proposition 4.5: local bilinear property and tensor density

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

/-- PDF p.14, Proposition 4.5: the local bilinear property gives projective-norm density. -/
theorem local_tensor_density (h : LocalBilinear K X Y) : TensorDense K X Y := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
