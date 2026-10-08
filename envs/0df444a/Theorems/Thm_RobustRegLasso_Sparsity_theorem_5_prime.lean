-- Prove2me | Theorems.Thm_RobustRegLasso_Sparsity_theorem_5_prime
-- name    : RobustRegLasso.Sparsity.theorem_5_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:52.044317+00:00
-- url     : https://prove2.me/theorems/e14c4240-e59b-47b6-b70a-a488fed0c4ed
-- title:
--   Theorem 5′ — an optimal $x^*$ supported on $I$ stays optimal for any $\tilde A$ within $l_j$ of $A$ off $I$, over the enlarged set $\tilde{\mathcal U}$
-- statement:
--   Let $a_1,\dots,a_m, b \in \mathbb R^n$ and radii $c_i \ge 0$, and let $\mathcal U = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c_i\}$. Let $x^*$ be an optimal solution of the robust regression problem
--   $$\min_{x\in\mathbb R^m}\Big\{\max_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2\Big\},$$
--   and let $I \subseteq \{1,\dots,m\}$ be such that $x^*_j = 0$ for all $j \notin I$. For numbers $l_j$ let
--   $$\tilde{\mathcal U} = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c_i,\ i\in I;\ \|\delta_j\|_2 \le c_j + l_j,\ j\notin I\}.$$
--   Then for every $\tilde A = (\tilde a_1,\dots,\tilde a_m)$ with $\|\tilde a_j - a_j\|_2 \le l_j$ for $j \notin I$ and $\tilde a_i = a_i$ for $i\in I$, $x^*$ is an optimal solution of
--   $$\min_{x\in\mathbb R^m}\Big\{\max_{\Delta A\in\tilde{\mathcal U}}\|b-(\tilde A+\Delta A)x\|_2\Big\}.$$
--
--   This is the main theorem of the paper's Section IV: Theorem 5 is its special case with $c_j = 0$ off $I$, and through Theorem 5 it yields the incoherence-type sparsity criterion of Theorem 6.
--
--   **Formalization Note** The radius vector $c$ is arbitrary (not fixed), so that Theorem 5 is a specialization. The paper does not state $l_j \ge 0$; it is implied by $\|\tilde a_j - a_j\|_2 \le l_j$, so $l$ is left unconstrained. The radii $c_i \ge 0$ are the paper's standing convention for (2) (with a negative radius $\mathcal U$ is empty and every $x$ is vacuously optimal, so the statement would fail). "Optimal" means minimizing the `EReal`-valued supremum over all of $\mathbb R^m$; existence of an optimal solution is assumed, not claimed. The paper's $\|\tilde a_j - a_j\|$ is the $\ell^2$ norm.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, pp. 8–9, Theorem 5′

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

namespace RobustRegLasso.Sparsity

theorem theorem_5_prime {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (xStar : Fin m → ℝ) (hopt : IsRobustSolution a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar)
    (I : Finset (Fin m)) (hx : ∀ j, j ∉ I → xStar j = 0) :
    ∀ aTilde : Fin m → EuclideanSpace ℝ (Fin n),
      (∀ j, j ∉ I → ‖aTilde j - a j‖ ≤ l j) → (∀ i, i ∈ I → aTilde i = a i) →
      IsRobustSolution aTilde b (enlargedSet c l I) xStar := by sorry

end RobustRegLasso.Sparsity
