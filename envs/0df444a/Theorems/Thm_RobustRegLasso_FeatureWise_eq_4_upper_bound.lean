-- Prove2me | Theorems.Thm_RobustRegLasso_FeatureWise_eq_4_upper_bound
-- name    : RobustRegLasso.FeatureWise.eq_4_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:53.218798+00:00
-- url     : https://prove2.me/theorems/e80bdad3-baac-48b7-8a7e-dd5e7f9570a3
-- title:
--   Eq. (4) — under any admissible disturbance, ‖b − (A + ΔA)x‖₂ ≤ ‖b − Ax‖₂ + Σ |xᵢ|cᵢ
-- statement:
--   Let $A\in\mathbb R^{n\times m}$ have columns $a_1,\dots,a_m$, let $b\in\mathbb R^n$, let $c_1,\dots,c_m\ge 0$, and let $\mathcal U$ be the feature-wise uncoupled uncertainty set $\{(\delta_1,\dots,\delta_m) : \|\delta_i\|_2\le c_i\}$ of (2). For every coefficient vector $x\in\mathbb R^m$ and every disturbance $\Delta A=(\delta_1,\dots,\delta_m)\in\mathcal U$,
--   $$\|b-(A+\Delta A)x\|_2 \;\le\; \|b-Ax\|_2 + \sum_{i=1}^m |x_i|\,c_i .$$
--
--   Taking the supremum over $\Delta A\in\mathcal U$, this is the upper half of the identity behind Theorem 1: the worst-case residual never exceeds the ℓ¹-regularized objective.
--
--   **Formalization Note** The paper's display (4) bounds the maximum over $\mathcal U$; the Lean statement gives the equivalent pointwise bound for each admissible disturbance, which avoids any supremum. The hypothesis $c_i\ge 0$ is the paper's standing assumption on (2).
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 4, Eq. (4), proof of Theorem 1

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

namespace RobustRegLasso.FeatureWise

theorem eq_4_upper_bound {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ)
    (δ : Fin m → EuclideanSpace ℝ (Fin n)) (hδ : δ ∈ uncertaintySet c) :
    perturbedResidual a δ b x ≤ ‖b - matVec a x‖ + ∑ i, |x i| * c i := by sorry

end RobustRegLasso.FeatureWise
