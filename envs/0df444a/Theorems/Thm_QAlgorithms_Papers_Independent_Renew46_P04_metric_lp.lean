-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_lp
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_lp
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:12:22.876229+00:00
-- url     : https://prove2.me/theorems/4ce65ec8-8acc-489c-af3e-8e8793bff760
-- title:
--   Example 4.12(b): Lp spaces
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For every measure $\mu$ and every finite exponent $1\le p<\infty$,
--
--   $$
--   L_p(\mu;\mathbb K)\text{ has the metric }\pi\text{ property}.
--   $$
--
--   No finiteness, semi-finiteness or sigma-finiteness hypothesis on the measure is imposed. The statement uses the actual $L_p$ norm and quotient by almost-everywhere equality.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 16, Example 4.12(b): Lp spaces

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

/-- PDF pp.16–19, Example 4.12(b): Lp for every measure, without finiteness or sigma-finiteness. -/
theorem metric_lp (A : Type*) [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p < ⊤) :
    MetricPi K (MeasureTheory.Lp K p mu) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
