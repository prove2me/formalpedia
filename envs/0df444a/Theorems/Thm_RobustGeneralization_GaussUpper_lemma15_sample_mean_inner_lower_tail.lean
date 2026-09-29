-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma15_sample_mean_inner_lower_tail
-- name    : RobustGeneralization.GaussUpper.lemma15_sample_mean_inner_lower_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:25:40.104128+00:00
-- url     : https://prove2.me/theorems/f41b66fa-8327-4ddf-9c20-3401a79e9d4d
-- title:
--   Lemma 15 — P[⟨z̄, µ⟩ ≤ ‖µ‖₂² − σ‖µ‖₂√(2 log(1/δ)/n)] ≤ δ
-- statement:
--   Let $z_1,\dots,z_n\in\mathbb R^d$ be i.i.d. with $z_i\sim\mathcal N_d(\mu,\sigma^2I)$, where $\mu\in\mathbb R^d$ is nonzero, $\sigma>0$ and $n\ge1$, and let $\bar z=\frac1n\sum_{i=1}^nz_i$. For every $\delta>0$,
--
--   $$\mathbb P\left[\langle\bar z,\mu\rangle\le\|\mu\|_2^2-\sigma\|\mu\|_2\sqrt{\frac{2\log(1/\delta)}{n}}\right]\le\delta.$$
--
--   The inner product of the sample mean with the true mean is, with high probability, not much smaller than $\|\mu\|_2^2$; together with Lemma 14 this lower-bounds the alignment of $\bar z/\|\bar z\|_2$ with $\mu$.
--
--   **Formalization Note** Two hypotheses are added. $n\ge1$: the sample mean has at least one sample. $\mu\neq0$: for $\mu=0$ the event is $0\le0$, of probability $1$, so the printed lemma is false for $\delta<1$; the paper applies it only with $\|\mu\|_2=\sqrt d$, $d\ge1$. For $\delta\ge1$ the square root of a non-positive number is $0$ and the bound is trivial.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 23, Lemma 15

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 15** (p. 23). For `z₁, …, zₙ` i.i.d. `N_d(µ, σ² I)`, `σ > 0`, `δ > 0`, the mean `z̄`
satisfies `P[⟨z̄, µ⟩ ≤ ‖µ‖₂² - σ‖µ‖₂ √(2 log(1/δ)/n)] ≤ δ`. The hypotheses `1 ≤ n` and `µ ≠ 0` are
added: at `µ = 0` the event is `0 ≤ 0`, of probability 1. -/
theorem lemma15_sample_mean_inner_lower_tail (d n : ℕ) (hn : 1 ≤ n) (μ : E d) (hμ : μ ≠ 0)
    (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (zbar' z) μ ≤
          ‖μ‖ ^ 2 - σ * ‖μ‖ * Real.sqrt (2 * Real.log (1 / δ) / n)} ≤
      ENNReal.ofReal δ := by sorry

end RobustGeneralization.GaussUpper
