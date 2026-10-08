-- Prove2me | Theorems.Thm_RobustRegLasso_FeatureWise_per_x_identity
-- name    : RobustRegLasso.FeatureWise.per_x_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:52.487778+00:00
-- url     : https://prove2.me/theorems/8a19472c-c269-4e49-9579-298c679ebd8e
-- title:
--   Proof of Theorem 1 — for every x, max over U of ‖b − (A + ΔA)x‖₂ equals ‖b − Ax‖₂ + Σ cᵢ|xᵢ|, attained
-- statement:
--   Let $n\ge1$, let $A\in\mathbb R^{n\times m}$ have columns $a_1,\dots,a_m$, let $b\in\mathbb R^n$, let $c_1,\dots,c_m\ge 0$, and let $\mathcal U=\{(\delta_1,\dots,\delta_m):\|\delta_i\|_2\le c_i\}$ be the uncertainty set (2). For every $x\in\mathbb R^m$ the worst-case residual is a maximum, and
--   $$\max_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2 = \|b-Ax\|_2 + \sum_{i=1}^m c_i|x_i| .$$
--   That is, the number $\|b-Ax\|_2+\sum_i c_i|x_i|$ belongs to the set $\{\|b-(A+\Delta A)x\|_2 : \Delta A\in\mathcal U\}$ and bounds it from above; equivalently, the robust objective $R(x)=\sup_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2$ equals the ℓ¹-regularized objective $L(x)$.
--
--   This per-point identity is the heart of Theorem 1: the robust regression objective and the ℓ¹-regularized objective are the same function of $x$.
--
--   **Formalization Note** "max" is stated as `IsGreatest` of the set of residual norms (the maximum exists and has this value), together with the equality of the `EReal` supremum $R(x)$ and $L(x)$. The paper leaves $n\ge1$ implicit; for $n=0$ the identity would read $0=\sum_i c_i|x_i|$ and is false, so `0 < n` is a hypothesis.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 4, proof of Theorem 1, first sentence ("Fix x∗. We prove that …") and closing sentence ("Combining Inequalities (4) and (5) …")

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

namespace RobustRegLasso.FeatureWise

theorem per_x_identity {n m : ℕ} (hn : 0 < n) (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ) :
    IsGreatest (residualValues a b c x) (‖b - matVec a x‖ + ∑ i, c i * |x i|) ∧
      robustObjective a b c x = ((‖b - matVec a x‖ + ∑ i, c i * |x i| : ℝ) : EReal) := by sorry

end RobustRegLasso.FeatureWise
