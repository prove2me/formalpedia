-- Prove2me | Theorems.Thm_RankOneBTF_lemma_3
-- name    : RankOneBTF.lemma_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:22:20.316275+00:00
-- url     : https://prove2.me/theorems/cf255785-3f82-42c6-905a-1611793c2c67
-- title:
--   Lemma 3 — tail bound for the product of two independent nonnegative random variables
-- statement:
--   Let $X_1,X_2$ be nonnegative independent random variables with $\mathbb E[X_1]>0$ and $\mathbb E[X_2]>0$. Suppose that for every $t>0$,
--   $$
--   \mathbb P\bigl[|X_1-\mathbb E[X_1]|\ge t\bigr]\le f_1(t),\qquad \mathbb P\bigl[|X_2-\mathbb E[X_2]|\ge t\bigr]\le f_2(t),\qquad(72)
--   $$
--   for some functions $f_1,f_2$. Then for any $t>0$,
--   $$
--   \mathbb P\bigl[|X_1X_2-\mathbb E[X_1X_2]|\ge t\bigr]\le f_1\Bigl(\frac{t}{\sqrt{t\,\mathbb E[X_2]/\mathbb E[X_1]}+2\,\mathbb E[X_2]}\Bigr)+f_2\Bigl(\frac{t}{\sqrt{t\,\mathbb E[X_1]/\mathbb E[X_2]}+2\,\mathbb E[X_1]}\Bigr).
--   $$
--
--   It turns concentration of two independent averages into concentration of their product, which is how Claims 5, 6 and 7 handle products of counts.
--
--   **Formalization Note** The random variables are measurable real functions on a probability space, assumed integrable so that the expectations exist.
--
--   Differences from the source:
--   - encoding: random variables with expectations → measurable and integrable real functions on a probability space; reason: the expectations in the statement must exist; no instance of the lemma is lost
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.2, Lemma 3, p.30, (72)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RankOneBTF

/-- **Lemma 3** (arXiv:2202.07053v3, §8.2, p.30): "Let X₁, X₂ be nonnegative independent random
variables with E[X₁] > 0 and E[X₂] > 0. Suppose that for every t > 0 we have
P[|X₁ − E[X₁]| ≥ t] ≤ f₁(t), P[|X₂ − E[X₂]| ≥ t] ≤ f₂(t), (72) for some functions f₁(·), f₂(·).
Then for any t > 0, we have
P[|X₁X₂ − E[X₁X₂]| ≥ t] ≤ f₁(t/(√(t E[X₂]/E[X₁]) + 2E[X₂])) + f₂(t/(√(t E[X₁]/E[X₂]) + 2E[X₁]))."

**Formalization Note** Random variables are measurable real functions on a probability space;
they are assumed integrable so that the expectations are defined. Probabilities are
`μ.real`. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X₁ X₂ : Ω → ℝ) (hm₁ : Measurable X₁) (hm₂ : Measurable X₂)
    (hi₁ : Integrable X₁ μ) (hi₂ : Integrable X₂ μ)
    (hnn₁ : ∀ ω, 0 ≤ X₁ ω) (hnn₂ : ∀ ω, 0 ≤ X₂ ω) (hind : IndepFun X₁ X₂ μ)
    (hE₁ : 0 < ∫ ω, X₁ ω ∂μ) (hE₂ : 0 < ∫ ω, X₂ ω ∂μ) (f₁ f₂ : ℝ → ℝ)
    (h₁ : ∀ t, 0 < t → μ.real {ω | t ≤ |X₁ ω - ∫ ω', X₁ ω' ∂μ|} ≤ f₁ t)
    (h₂ : ∀ t, 0 < t → μ.real {ω | t ≤ |X₂ ω - ∫ ω', X₂ ω' ∂μ|} ≤ f₂ t)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ |X₁ ω * X₂ ω - ∫ ω', X₁ ω' * X₂ ω' ∂μ|} ≤
      f₁ (t / (Real.sqrt (t * (∫ ω, X₂ ω ∂μ) / ∫ ω, X₁ ω ∂μ) + 2 * ∫ ω, X₂ ω ∂μ)) +
      f₂ (t / (Real.sqrt (t * (∫ ω, X₁ ω ∂μ) / ∫ ω, X₂ ω ∂μ) + 2 * ∫ ω, X₁ ω ∂μ)) := by sorry

end RankOneBTF
