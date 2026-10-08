-- Prove2me | Theorems.Thm_RobustRegLasso_FeatureWise_eq_5_worst_case_attained
-- name    : RobustRegLasso.FeatureWise.eq_5_worst_case_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:58.742382+00:00
-- url     : https://prove2.me/theorems/11d86722-4d25-4246-9ece-04cd4f339cf4
-- title:
--   Eq. (5) — the disturbance δ*ᵢ = −cᵢ sgn(xᵢ)u is admissible and attains ‖b − Ax‖₂ + Σ cᵢ|xᵢ|
-- statement:
--   Let $n\ge 1$, let $A\in\mathbb R^{n\times m}$ have columns $a_1,\dots,a_m$, let $b\in\mathbb R^n$, let $c_1,\dots,c_m\ge 0$, and let $x\in\mathbb R^m$. Let $u\in\mathbb R^n$ be a unit vector, $\|u\|_2=1$, chosen as
--   $$u = \frac{b-Ax}{\|b-Ax\|_2}\quad\text{if } Ax\ne b,$$
--   and arbitrary (of unit norm) if $Ax=b$. Define $\delta_i^* = -c_i\,\mathrm{sgn}(x_i)\,u$ for $i=1,\dots,m$ (with $\mathrm{sgn}(0)=0$) and $\Delta A^*=(\delta_1^*,\dots,\delta_m^*)$. Then $\Delta A^*$ lies in the uncertainty set $\mathcal U=\{(\delta_1,\dots,\delta_m):\|\delta_i\|_2\le c_i\}$ of (2), and
--   $$\|b-(A+\Delta A^*)x\|_2 = \|b-Ax\|_2 + \sum_{i=1}^m c_i|x_i| .$$
--
--   This is the lower half of the identity behind Theorem 1: an explicit admissible disturbance pushes the residual all the way up to the ℓ¹-regularized objective, so the bound (4) is attained.
--
--   **Formalization Note** The paper leaves $n\ge 1$ implicit; it is needed for a unit vector $u$ to exist and is stated as `0 < n`. The choice of $u$ is universally quantified: any unit $u$ that equals $(b-Ax)/\|b-Ax\|_2$ whenever $Ax\ne b$. The sign function is `Real.sign`, with $\mathrm{sgn}(0)=0$ as the computation in (5) requires.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 4, Eq. (5) and the definitions of u and δ*ᵢ preceding it, proof of Theorem 1

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

namespace RobustRegLasso.FeatureWise

theorem eq_5_worst_case_attained {n m : ℕ} (hn : 0 < n) (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (hu_dir : matVec a x ≠ b → u = ‖b - matVec a x‖⁻¹ • (b - matVec a x)) :
    worstCaseDisturbance c x u ∈ uncertaintySet c ∧
      perturbedResidual a (worstCaseDisturbance c x u) b x =
        ‖b - matVec a x‖ + ∑ i, c i * |x i| := by sorry

end RobustRegLasso.FeatureWise
