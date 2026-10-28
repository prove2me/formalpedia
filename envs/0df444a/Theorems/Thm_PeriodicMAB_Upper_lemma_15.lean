-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_15
-- name    : PeriodicMAB.Upper.lemma_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:16.401877+00:00
-- url     : https://prove2.me/theorems/a2fe01d2-8b6f-4d76-af67-8daa33504d64
-- title:
--   Lemma 15, p. 39 — anytime bound $P(\exists t\ge1,\ |q_t|\ge\sqrt{(4\sigma^2/t)\log(4t/\delta_0)})\le\delta_0$
-- statement:
--   Let $X_1,X_2,\dots$ be independent sub-Gaussian random variables with parameter $\sigma>0$, i.e. $\mathbb E[e^{\lambda X_t}]\le e^{\sigma^2\lambda^2/2}$ for all real $\lambda$, and let $q_t=\frac1t\sum_{j=1}^tX_j$. For every $\delta_0\in(0,1)$,
--   $$
--   \mathbb P\Big(\exists t\ge1:\ |q_t|\ge\sqrt{\frac{4\sigma^2}{t}\log\frac{4t}{\delta_0}}\Big)\le\delta_0 .
--   $$
--
--   This anytime concentration inequality, uniform over all sample sizes, is what makes the confidence widths (10) and (17) valid for the adaptively growing sample sets of Algorithm 2.
--
--   **Formalization Note** The variables are indexed by $\mathbb N$ and independence is required of the whole family; $X_0$ never enters $q_t$. Sub-Gaussianity is Mathlib's `HasSubgaussianMGF` with variance proxy $\sigma^2$ (which includes integrability of $e^{\lambda X_t}$).
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 39, Lemma 15

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 15 (p. 39): for independent sub-Gaussian `X₁, X₂, …` with parameter `σ` and
`q_t = (1/t) ∑_{j=1}^t X_j`, `P(∃ t ≥ 1, |q_t| ≥ √((4σ²/t) log(4t/δ₀))) ≤ δ₀` for `δ₀ ∈ (0,1)`. -/
theorem lemma_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hindep : iIndepFun X P)
    (hX : ∀ t, HasSubgaussianMGF (X t) (σ ^ 2) P) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) :
    P {ω | ∃ t : ℕ, 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} ≤ ENNReal.ofReal δ₀ := by sorry

end PeriodicMAB.Upper
