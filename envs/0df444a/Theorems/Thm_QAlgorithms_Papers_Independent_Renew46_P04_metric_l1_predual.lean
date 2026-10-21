-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_l1_predual
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_l1_predual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:12:52.939519+00:00
-- url     : https://prove2.me/theorems/3f505ee4-2f6e-4ba2-b981-995bd1453ec5
-- title:
--   Example 4.12(c): L1 preduals
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For any measure $\mu$, if the continuous dual of $X$ is linearly isometric to $L_1(\mu;\mathbb K)$, then
--
--   $$
--   X^*\simeq_{\mathrm{lin.iso.}}L_1(\mu;\mathbb K)\quad\Longrightarrow\quad X\text{ has metric }\pi.
--   $$
--
--   The preduality is isometric, and the measure is arbitrary rather than fixed to Lebesgue measure.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 17, Example 4.12(c): L1 preduals

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

/-- PDF pp.16–19, Example 4.12(c): an isometric L1 predual for an arbitrary measure. -/
theorem metric_l1_predual (X A : Type*) [NormedAddCommGroup X] [NormedSpace K X]
    [CompleteSpace X] [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    (E : (X →L[K] K) ≃ₗᵢ[K] MeasureTheory.Lp K 1 mu) : MetricPi K X := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
