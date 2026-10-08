-- Prove2me | Theorems.Thm_RobustRegLasso_Sparsity_theorem_5_prime_inclusion
-- name    : RobustRegLasso.Sparsity.theorem_5_prime_inclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:34.878335+00:00
-- url     : https://prove2.me/theorems/e93d89d3-6895-4efd-be71-7fe3d126b56e
-- title:
--   Proof of Theorem 5′, second display — $A+\mathcal U\subseteq\tilde A+\tilde{\mathcal U}$ as sets of perturbed matrices, hence $R_{\tilde A,\tilde{\mathcal U}}\ge R_{A,\mathcal U}$
-- statement:
--   Let $a_1,\dots,a_m, \tilde a_1,\dots,\tilde a_m, b \in \mathbb R^n$, radii $c_i$, numbers $l_j$, and an index set $I \subseteq \{1,\dots,m\}$, with $\|a_j - \tilde a_j\|_2 \le l_j$ for $j \notin I$ and $a_i = \tilde a_i$ for $i \in I$. Then
--   $$\{A + \Delta A \mid \Delta A \in \mathcal U\} \subseteq \{\tilde A + \Delta A \mid \Delta A \in \tilde{\mathcal U}\},$$
--   and consequently, for every $x' \in \mathbb R^m$,
--   $$\max_{\Delta A\in\tilde{\mathcal U}} \|b-(\tilde A+\Delta A)x'\|_2 \ \ge\ \max_{\Delta A\in\mathcal U} \|b-(A+\Delta A)x'\|_2.$$
--
--   This is the second step of the proof of Theorem 5′: enlarging the bounds on the features outside $I$ by $l_j$ absorbs the change from $A$ to $\tilde A$, so the worst case for $(\tilde A, \tilde{\mathcal U})$ dominates the worst case for $(A, \mathcal U)$ at every point.
--
--   **Formalization Note** The printed display reads $\max_{\Delta A\in\tilde{\mathcal U}}\|b-(A+\Delta A)x'\|_2 \ge \max_{\Delta A\in\mathcal U}\|b-(\tilde A+\Delta A)x'\|_2$, with $A$ and $\tilde A$ exchanged relative to the inclusion that justifies it and to the final display of the proof that uses it. The version stated here is the one the inclusion gives and the proof uses (the printed one is also true, by the symmetric inclusion). Matrices are column families, so $A + \Delta A$ is the family $(a_i + \delta_i)_i$. Maxima are suprema in `EReal`. No sign condition on $c$ or $l$ is needed.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 9, proof of Theorem 5′, second display and inclusion

import Mathlib
import Definitions.Def_RobustRegLasso_Sparsity_Basic

namespace RobustRegLasso.Sparsity

theorem theorem_5_prime_inclusion {n m : ℕ} (a aTilde : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c l : Fin m → ℝ) (I : Finset (Fin m))
    (hl : ∀ j, j ∉ I → ‖a j - aTilde j‖ ≤ l j) (hI : ∀ i, i ∈ I → a i = aTilde i) :
    {M | ∃ δ ∈ (RobustRegLasso.FeatureWise.uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))), M = a + δ} ⊆
      {M | ∃ δ ∈ (enlargedSet c l I : Set (Fin m → EuclideanSpace ℝ (Fin n))), M = aTilde + δ} ∧
    ∀ x' : Fin m → ℝ, robustObjective a b (RobustRegLasso.FeatureWise.uncertaintySet c) x' ≤
      robustObjective aTilde b (enlargedSet c l I) x' := by sorry

end RobustRegLasso.Sparsity
