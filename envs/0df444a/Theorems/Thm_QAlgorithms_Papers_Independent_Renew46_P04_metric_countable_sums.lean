-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_countable_sums
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.metric_countable_sums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:13:15.399651+00:00
-- url     : https://prove2.me/theorems/10912726-c5c3-43b3-9c0a-e3404595a43f
-- title:
--   Example 4.12(e): countable c0 and ℓp sums
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Let $(X_n)_{n\in\mathbb N}$ be Banach spaces, each having metric $\pi$. Then their $c_0$ sum and every finite-exponent $\ell_p$ sum, $1\le p<\infty$, have metric $\pi$:
--
--   $$
--   \left(\bigoplus_nX_n\right)_{c_0}\text{ and }\left(\bigoplus_nX_n\right)_{\ell_p}\text{ have metric }\pi.
--   $$
--
--   The $c_0$ sum is constructed as the sup-norm closure of the finite-support vectors. The unrestricted $\ell_\infty$ sum is excluded.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 17, Example 4.12(e): countable c0 and ℓp sums

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

/-- PDF pp.16–18, Example 4.12(e): countable c0 sums and finite-exponent lp sums. -/
theorem metric_countable_sums (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace K (E n)] [∀ n, CompleteSpace (E n)] (h : ∀ n, MetricPi K (E n)) :
    MetricPi K (CZeroSum (K := K) (E := E)) ∧
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p < ⊤ → MetricPi K (lp E p) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P04

end
