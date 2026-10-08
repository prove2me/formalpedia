-- Prove2me | Theorems.Thm_RobustRegLasso_FeatureWise_theorem_1_robust_eq_l1_regularized
-- name    : RobustRegLasso.FeatureWise.theorem_1_robust_eq_l1_regularized
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:55.232908+00:00
-- url     : https://prove2.me/theorems/b5d5a541-c5d4-416e-8ce3-d3f2e80e83a7
-- title:
--   Theorem 1 — robust regression with feature-wise uncertainty set (2) is equivalent to ℓ¹-regularized regression (3)
-- statement:
--   Let $n\ge 1$ and $m$ be integers, let $A\in\mathbb R^{n\times m}$ have columns $a_1,\dots,a_m$, let $b\in\mathbb R^n$, and let $c_1,\dots,c_m\ge 0$. Let $\mathcal U=\{(\delta_1,\dots,\delta_m):\|\delta_i\|_2\le c_i,\ i=1,\dots,m\}$ be the feature-wise uncoupled uncertainty set (2). Then the robust regression problem (1),
--   $$\min_{x\in\mathbb R^m}\Bigl\{\max_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2\Bigr\},$$
--   is equivalent to the ℓ¹-regularized regression problem (3),
--   $$\min_{x\in\mathbb R^m}\Bigl\{\|b-Ax\|_2+\sum_{i=1}^m c_i|x_i|\Bigr\}.$$
--   Precisely:
--   1. a vector $x\in\mathbb R^m$ minimizes the robust objective $R(x)=\sup_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2$ if and only if it minimizes $L(x)=\|b-Ax\|_2+\sum_i c_i|x_i|$;
--   2. the two problems have the same optimal value, $\inf_x R(x)=\inf_x L(x)$.
--
--   The theorem identifies robustness to feature-wise bounded perturbations of the data matrix with ℓ¹ regularization: with equal budgets $c_i=c$ it is the Lasso with the unsquared loss.
--
--   **Formalization Note** "Equivalent" is read as in the proof ("Minimizing over $x$ on both sides proves the theorem"): same minimizers and same optimal value. No minimizer is claimed to exist, since the paper does not show one. The robust objective $R$ is the supremum over $\mathcal U$ in `EReal`, and the optimal values are infima in `EReal`, so neither carries a junk value. The paper leaves $n\ge1$ implicit; it is a hypothesis (`0 < n`). The budgets $c_i\ge0$ are the paper's standing assumption on (2).
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 4, Theorem 1

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

namespace RobustRegLasso.FeatureWise

theorem theorem_1_robust_eq_l1_regularized {n m : ℕ} (hn : 0 < n)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (∀ x : Fin m → ℝ, IsMinOn (robustObjective a b c) Set.univ x ↔
        IsMinOn (l1RegularizedObjective a b c) Set.univ x) ∧
      ⨅ x : Fin m → ℝ, robustObjective a b c x =
        ⨅ x : Fin m → ℝ, ((l1RegularizedObjective a b c x : ℝ) : EReal) := by sorry

end RobustRegLasso.FeatureWise
