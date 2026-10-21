-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_projective_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_projective_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:13:49.443044+00:00
-- url     : https://prove2.me/theorems/e690ec9e-4664-4788-8310-18eb1889a281
-- title:
--   Example 4.12(f): projective products
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If $X$ and $Y$ both have metric $\pi$, then
--
--   $$
--   X\widehat\otimes_\pi Y\text{ has metric }\pi.
--   $$
--
--   The conclusion concerns the actual completed projective product and common finite-dimensional projection ranges for finite test sets.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 17, Example 4.12(f): projective products

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

/-- PDF pp.16–19, Example 4.12(f): stability of metric pi under completed projective products. -/
theorem metric_projective_product [CompleteSpace X] [CompleteSpace Y] (hX : MetricPi K X) (hY : MetricPi K Y) :
    MetricPi K (Projective K X Y) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
