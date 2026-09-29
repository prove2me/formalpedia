-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_fact12_gaussian_norm_tail
-- name    : RobustGeneralization.GaussUpper.fact12_gaussian_norm_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:23:41.444438+00:00
-- url     : https://prove2.me/theorems/b50e0621-ae20-4f1d-9a09-4314d60cc4ec
-- title:
--   Fact 12 — Gaussian norm tail: P[‖z‖₂ ≥ σ√d + t] ≤ exp(−t²/(2σ²))
-- statement:
--   Let $z\in\mathbb R^d$ be drawn from a centered spherical Gaussian, $z\sim\mathcal N_d(0,\sigma^2I)$ with $\sigma>0$, and let $t\ge0$. Then
--
--   $$\mathbb P\big[\|z\|_2\ge\sigma\sqrt d+t\big]\le e^{-t^2/(2\sigma^2)}.$$
--
--   The Euclidean norm of a Gaussian vector concentrates at scale $\sigma$ above $\sigma\sqrt d$, independently of the dimension. The paper uses it to control the norm of a sample mean (Lemma 13).
--
--   **Formalization Note** The hypothesis $t\ge0$ is added: the printed statement quantifies over no range of $t$, and for $t=-\sigma\sqrt d$ its left side is $1$ while its right side is $e^{-d/2}<1$. The paper's proof is the $t\ge0$ concentration bound.
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 22, Fact 12

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Fact 12** (Schmidt et al., arXiv:1804.11285v2, p. 22). For `z ∼ N_d(0, σ² I)` with `σ > 0`,
`P[‖z‖₂ ≥ σ√d + t] ≤ exp(-t²/(2σ²))`. The hypothesis `0 ≤ t` is added: the printed bound is false
for `t = -σ√d`. -/
theorem fact12_gaussian_norm_tail (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (ht : 0 ≤ t) :
    gaussVec (0 : E d) σ {z | σ * Real.sqrt d + t ≤ ‖z‖} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ ^ 2))) := by sorry

end RobustGeneralization.GaussUpper
