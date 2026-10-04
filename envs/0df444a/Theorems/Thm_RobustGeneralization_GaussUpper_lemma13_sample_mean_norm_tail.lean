-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma13_sample_mean_norm_tail
-- name    : RobustGeneralization.GaussUpper.lemma13_sample_mean_norm_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:24:19.638986+00:00
-- url     : https://prove2.me/theorems/06ac9a03-baec-438c-977b-17ad18cbad41
-- title:
--   Lemma 13 — norm of a Gaussian sample mean: P[‖z̄‖₂ ≥ ‖µ‖₂ + σ(√d + √(2 log 1/δ))/√n] ≤ δ
-- statement:
--   Let $z_1,\dots,z_n\in\mathbb R^d$ be i.i.d. with $z_i\sim\mathcal N_d(\mu,\sigma^2I)$, where $\mu\in\mathbb R^d$, $\sigma>0$ and $n\ge1$, and let $\bar z=\frac1n\sum_{i=1}^nz_i$ be the sample mean. For every target probability $\delta>0$,
--
--   $$\mathbb P\left[\|\bar z\|_2\ge\|\mu\|_2+\frac{\sigma\big(\sqrt d+\sqrt{2\log(1/\delta)}\big)}{\sqrt n}\right]\le\delta.$$
--
--   This controls how far the norm of the sample mean can exceed the norm of the true mean; it is the upper half of the estimate that makes the normalized mean $\widehat w=\bar z/\|\bar z\|_2$ well aligned with $\mu$.
--
--   **Formalization Note** The hypothesis $n\ge1$ is added (the paper's sample mean has at least one sample; at $n=0$ Lean's conventions make $\bar z=0$ and the statement false for $\mu=0$). For $\delta\ge1$ the square root of the non-positive number $2\log(1/\delta)$ is taken as $0$, and the bound holds trivially.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 22, Lemma 13

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 13** (p. 22). For `z₁, …, zₙ` i.i.d. `N_d(µ, σ² I)`, `σ > 0`, `δ > 0`, the sample mean
`z̄` satisfies `P[‖z̄‖₂ ≥ ‖µ‖₂ + σ(√d + √(2 log(1/δ)))/√n] ≤ δ`. The hypothesis `1 ≤ n` is added
(a sample mean of at least one sample). -/
theorem lemma13_sample_mean_norm_tail (d n : ℕ) (hn : 1 ≤ n) (μ : E d) (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | ‖μ‖ + σ * (Real.sqrt d + Real.sqrt (2 * Real.log (1 / δ))) / Real.sqrt n ≤
          ‖zbar' z‖} ≤
      ENNReal.ofReal δ := by sorry

end RobustGeneralization.GaussUpper
