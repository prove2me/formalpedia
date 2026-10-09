-- Prove2me | Theorems.Thm_SLPricing_PreAnn_lemma_1
-- name    : SLPricing.PreAnn.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:51.707642+00:00
-- url     : https://prove2.me/theorems/1674498d-2cf7-4696-ae70-9a21215b4898
-- title:
--   Lemma 1, p. 10 — the pre-posterior law of the posterior mean is $N(0,\sigma_p^2 n_1\gamma/(n_1\gamma+1))$
-- statement:
--   Let the product's mean quality $\hat q$ have the prior law $N(0,\sigma_p^2)$ with $\sigma_p>0$, and suppose a mass $n_1>0$ of first-period buyers post reviews whose average rating is $R=\hat q+\varepsilon$, where the sampling noise $\varepsilon\sim N(0,\sigma_q^2/n_1)$, $\sigma_q>0$, is independent of $\hat q$ (equivalently $R\mid\hat q\sim N(\hat q,\sigma_q^2/n_1)$). With $\gamma=\sigma_p^2/\sigma_q^2$, the posterior mean (1) is
--   $$q_u=\frac{n_1\gamma}{n_1\gamma+1}\,R .$$
--   Then, seen ex ante, $q_u$ is Normally distributed:
--   $$q_u\sim N\!\left(0,\ \sigma_p^2\,\frac{n_1\gamma}{n_1\gamma+1}\right),$$
--   and this law coincides with the model's pre-posterior law for a mass $n_1$ of reviews.
--
--   The lemma is the source of the pre-posterior law used throughout: the variance of $q_u$ grows with the number of reviews, which is what makes waiting more valuable when more consumers buy early.
--
--   **Formalization Note** $\hat q$ and $\varepsilon$ are measurable random variables on a probability space; the laws are Mathlib's `gaussianReal`. The case $n_1=0$ (no reviews, $q_u=0$) is excluded here because the noise variance $\sigma_q^2/n_1$ is undefined; the model file sets the law to the point mass at $0$ in that case, as the paper does on p. 11.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 1, p. 10; (1), p. 9; proof of Lemma 1, pp. 27–28

import Mathlib
import Definitions.Def_SLPricing_PreAnn_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- Lemma 1, p. 10 (proof pp. 27–28): the pre-posterior law of the posterior mean.
The mean quality `q̂` has prior law `N(0, σp²)`; the average rating `R` of a mass `n₁ > 0` of
reviews is `q̂ + ε` with noise `ε ∼ N(0, σq²/n₁)` independent of `q̂` (i.e. `R | q̂ ∼ N(q̂, σq²/n₁)`);
the posterior mean (1) is `q_u = n₁γ/(n₁γ + 1) · R` with `γ = σp²/σq²`. Then `q_u` is Normal with
mean `0` and variance `σp² · n₁γ/(n₁γ + 1)`, which is the layer's `prePost`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σp σq γ n₁ : ℝ) (hσp : 0 < σp) (hσq : 0 < σq) (hγ : γ = σp ^ 2 / σq ^ 2) (hn₁ : 0 < n₁)
    (qhat ε : Ω → ℝ) (hqm : Measurable qhat) (hεm : Measurable ε)
    (hqlaw : μ.map qhat = gaussianReal 0 (σp ^ 2).toNNReal)
    (hεlaw : μ.map ε = gaussianReal 0 (σq ^ 2 / n₁).toNNReal)
    (hind : IndepFun qhat ε μ) :
    μ.map (fun ω => n₁ * γ / (n₁ * γ + 1) * (qhat ω + ε ω)) =
        gaussianReal 0 (σp ^ 2 * (n₁ * γ / (n₁ * γ + 1))).toNNReal ∧
      ∀ P : Params, P.σp = σp → P.γ = γ →
        μ.map (fun ω => n₁ * γ / (n₁ * γ + 1) * (qhat ω + ε ω)) = prePost P n₁ := by sorry

end SLPricing.PreAnn
