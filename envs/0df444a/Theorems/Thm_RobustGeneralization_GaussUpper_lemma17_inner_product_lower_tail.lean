-- Prove2me | Theorems.Thm_RobustGeneralization_GaussUpper_lemma17_inner_product_lower_tail
-- name    : RobustGeneralization.GaussUpper.lemma17_inner_product_lower_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:26:37.959784+00:00
-- url     : https://prove2.me/theorems/b1be64a1-3e2d-4f7f-b757-6e73537183d7
-- title:
--   Lemma 17 — for a unit w with ⟨w, µ⟩ ≥ ρ ≥ 0: P[⟨w, z⟩ ≤ ρ] ≤ exp(−(⟨w, µ⟩ − ρ)²/(2σ²))
-- statement:
--   Let $z\sim\mathcal N_d(\mu,\sigma^2I)$ with $\mu\in\mathbb R^d$ and $\sigma>0$, and let $w\in\mathbb R^d$ be a unit vector ($\|w\|_2=1$) with $\langle w,\mu\rangle\ge\rho$ for some $\rho\ge0$. Then
--
--   $$\mathbb P\big[\langle w,z\rangle\le\rho\big]\le\exp\left(-\frac{(\langle w,\mu\rangle-\rho)^2}{2\sigma^2}\right).$$
--
--   The lemma converts alignment of a linear classifier with the class mean into a bound on the probability that a Gaussian point falls within margin $\rho$ of its decision boundary; with $\rho=0$ it bounds the classification error, and with $\rho=\varepsilon\|w\|_p^*$ the robust error (Lemma 20).
-- source:
--   Schmidt et al., Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 24, Lemma 17

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- **Lemma 17** (p. 24). For `z ∼ N_d(µ, σ² I)`, `σ > 0`, and a unit vector `w` with
`⟨w, µ⟩ ≥ ρ ≥ 0`, `P[⟨w, z⟩ ≤ ρ] ≤ exp(-(⟨w, µ⟩ - ρ)²/(2σ²))`. -/
theorem lemma17_inner_product_lower_tail (d : ℕ) (μ : E d) (σ : ℝ) (hσ : 0 < σ) (w : E d)
    (hw : ‖w‖ = 1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hwμ : ρ ≤ inner ℝ w μ) :
    gaussVec μ σ {z | inner ℝ w z ≤ ρ} ≤
      ENNReal.ofReal (Real.exp (-(inner ℝ w μ - ρ) ^ 2 / (2 * σ ^ 2))) := by sorry

end RobustGeneralization.GaussUpper
