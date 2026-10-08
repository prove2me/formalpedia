-- Prove2me | Theorems.Thm_RobustRegLasso_Sparsity_theorem_5_sparse_solution
-- name    : RobustRegLasso.Sparsity.theorem_5_sparse_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:30.462924+00:00
-- url     : https://prove2.me/theorems/09d6dd63-2360-413b-b3de-86bb28014c99
-- title:
--   Theorem 5 — robust regression has a solution supported on $I$ if some allowable perturbation of the features outside $I$ makes them irrelevant
-- statement:
--   Let $a_1,\dots,a_m, b \in \mathbb R^n$, radii $c_i \ge 0$, and $\mathcal U = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c_i\}$, the feature-wise uncoupled uncertainty set. Let $I \subseteq \{1,\dots,m\}$, and write $\mathcal U^I = \{\Delta A^I \mid \Delta A \in \mathcal U\}$, where $\Delta A^I$ agrees with $\Delta A$ on the features in $I$ and is zero elsewhere.
--
--   Suppose there is a perturbation $\Delta\tilde A^{I^c} \in \mathcal U$ of the features in $I^c$ (that is, zero on every feature in $I$) such that the robust regression problem
--   $$\min_{x\in\mathbb R^m}\Big\{\max_{\Delta\tilde A^I\in\mathcal U^I}\|b-(A+\Delta\tilde A^{I^c}+\Delta\tilde A^I)x\|_2\Big\}$$
--   has a solution supported on $I$. Then the robust regression problem
--   $$\min_{x\in\mathbb R^m}\Big\{\max_{\Delta A\in\mathcal U}\|b-(A+\Delta A)x\|_2\Big\}$$
--   has a solution supported on $I$: some optimal solution $x^*$ has $x^*_j = 0$ for all $j \notin I$.
--
--   In words, a robust regression has an optimal solution supported on $I$ if some allowable perturbation of the features outside $I$ makes them irrelevant. This connects robustness to sparsity, and is the tool from which the paper derives its incoherence-type criterion (Theorem 6).
--
--   **Formalization Note** "Has a solution supported on $I$" is the existence of a minimizer of the robust objective (the `EReal` supremum over the set) with zero entries off $I$. The perturbation $\Delta\tilde A^{I^c}$ is encoded as an element of $\mathcal U$ that vanishes on $I$. The radii $c_i \ge 0$ are the paper's standing convention. The paper writes $I \subseteq\{1,\dots,n\}$ on p. 8; features are indexed by $1,\dots,m$.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 8, Theorem 5

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

namespace RobustRegLasso.Sparsity

theorem theorem_5_sparse_solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (I : Finset (Fin m))
    (h : ∃ δTilde ∈ (RobustRegLasso.FeatureWise.uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))),
      (∀ i, i ∈ I → δTilde i = 0) ∧
      HasSolutionSupportedOn (a + δTilde) b (restrictedSet c I) I) :
    HasSolutionSupportedOn a b (RobustRegLasso.FeatureWise.uncertaintySet c) I := by sorry

end RobustRegLasso.Sparsity
