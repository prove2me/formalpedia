-- Prove2me | Theorems.Thm_RobinsonFP_Convergence_ineq1
-- name    : RobinsonFP.Convergence.ineq1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:34.681981+00:00
-- url     : https://prove2.me/theorems/b92c6ae8-8104-4b81-9796-9f7d9db734a0
-- title:
--   (1) — min_j Σ_i a_ij x_i ≤ max_i Σ_j a_ij y_j for all mixed strategies
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ pay-off matrix with $m, n \ge 1$. For every probability vector $x = (x_1,\dots,x_m)$ of the first player ($x_i \ge 0$, $\sum_i x_i = 1$) and every probability vector $y = (y_1, \dots, y_n)$ of the second player ($y_j \ge 0$, $\sum_j y_j = 1$),
--   $$\min_j \sum_i a_{ij} x_i \;\le\; \max_i \sum_j a_{ij} y_j .$$
--
--   The left side is the payoff the first player guarantees with $x$, the right side the loss the second player concedes at most with $y$. This weak duality inequality is used in Lemma 1, in Lemma 3 (for the transpose of $A$), and at the end of the proof of the Theorem.
--
--   **Formalization Note** Probability vectors are elements of Mathlib's `stdSimplex`. Rows and columns are indexed by finite nonempty types.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), p. 296, inequality (1)

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 296, inequality (1): for all probability vectors `x` (over rows) and `y`
(over columns), `min_j Σ_i a_ij x_i ≤ max_i Σ_j a_ij y_j`. -/
theorem ineq1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∀ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ κ,
      vmin (fun j => ∑ i, A i j * x i) ≤ vmax (fun i => ∑ j, A i j * y j) := by sorry

end RobinsonFP.Convergence
