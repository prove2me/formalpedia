-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_injective_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_injective_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:14:16.783204+00:00
-- url     : https://prove2.me/theorems/53b2bab1-9375-4405-ae26-eccd9726473f
-- title:
--   Example 4.12(g): injective products
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $X$ and $Y$ both have metric $\pi$, then
--
--   $$
--   X\widehat\otimes_\varepsilon Y\text{ has metric }\pi.
--   $$
--
--   The injective product is the norm-closed algebraic image in bounded bilinear forms on the duals. Its norm is the supremum of absolute values over the two dual unit balls, as in the source.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 17, Example 4.12(g): injective products

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

section InjectiveProduct

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

/-- PDF pp.16–19, Example 4.12(g): metric pi stability under the completed injective product. -/
theorem metric_injective_product [CompleteSpace X] [CompleteSpace Y] (hX : MetricPi K X) (hY : MetricPi K Y) :
    MetricPi K (InjectiveProduct (K := K) (X := X) (Y := Y)) := by sorry

end InjectiveProduct

end QAlgorithms.Papers.Independent.Renew46.P04

end
