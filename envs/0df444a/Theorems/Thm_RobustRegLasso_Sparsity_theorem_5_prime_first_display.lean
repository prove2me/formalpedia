-- Prove2me | Theorems.Thm_RobustRegLasso_Sparsity_theorem_5_prime_first_display
-- name    : RobustRegLasso.Sparsity.theorem_5_prime_first_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:20.129977+00:00
-- url     : https://prove2.me/theorems/6b4c0fac-0b48-4e11-8320-efd581dcf534
-- title:
--   Proof of Theorem 5′, first display — at $x^*$ supported on $I$, the worst cases over $\tilde{\mathcal U}$ and $\mathcal U$, for $A$ and $\tilde A$, coincide
-- statement:
--   Let $a_1,\dots,a_m, b \in \mathbb R^n$, radii $c_i \ge 0$, numbers $l_j$, and an index set $I \subseteq \{1,\dots,m\}$. Let $\tilde A$ have columns $\tilde a_i$ with $\tilde a_i = a_i$ for $i \in I$ and $\|\tilde a_j - a_j\|_2 \le l_j$ for $j \notin I$. Let $x^* \in \mathbb R^m$ satisfy $x^*_j = 0$ for all $j \notin I$. With $\mathcal U$ the feature-wise set with radii $c$ and $\tilde{\mathcal U}$ the enlarged set of Theorem 5′,
--   $$\max_{\Delta A\in\tilde{\mathcal U}} \|b-(A+\Delta A)x^*\|_2 = \max_{\Delta A\in\mathcal U} \|b-(A+\Delta A)x^*\|_2 = \max_{\Delta A\in\mathcal U} \|b-(\tilde A+\Delta A)x^*\|_2,$$
--   and moreover
--   $$\max_{\Delta A\in\tilde{\mathcal U}} \|b-(\tilde A+\Delta A)x^*\|_2 = \max_{\Delta A\in\mathcal U} \|b-(A+\Delta A)x^*\|_2.$$
--   No optimality of $x^*$ is assumed.
--
--   This is the first step of the proof of Theorem 5′: since $x^*$ puts no weight on the features outside $I$, the columns $j \notin I$ of both $\tilde A$ and $\Delta A$ have no effect on the residual, so changing them (or the bounds on them) does not change the worst case at $x^*$.
--
--   **Formalization Note** The page displays the first three quantities; the proof of Theorem 5′ then uses the fourth equality ($\tilde A$ and $\tilde{\mathcal U}$ together), which holds for the same reason, so it is stated as an additional conjunct. The maxima are suprema in `EReal`. The hypothesis $\|\tilde a_j - a_j\|_2 \le l_j$ is used only to force $c_j + l_j \ge 0$ (so $\tilde{\mathcal U}$ is not empty); the radii $c_i \ge 0$ are the paper's standing convention.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 9, proof of Theorem 5′, first display

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

namespace RobustRegLasso.Sparsity

theorem theorem_5_prime_first_display {n m : ℕ} (a aTilde : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i)
    (I : Finset (Fin m)) (xStar : Fin m → ℝ) (hx : ∀ j, j ∉ I → xStar j = 0)
    (hl : ∀ j, j ∉ I → ‖aTilde j - a j‖ ≤ l j) (hI : ∀ i, i ∈ I → aTilde i = a i) :
    robustObjective a b (enlargedSet c l I) xStar = robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar =
      robustObjective aTilde b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar ∧
    robustObjective aTilde b (enlargedSet c l I) xStar =
      robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) xStar := by sorry

end RobustRegLasso.Sparsity
