-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_lagrangean_separates_into_knapsacks
-- name    : RossSolandGAP.Bound.lagrangean_separates_into_knapsacks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:09:48.465986+00:00
-- url     : https://prove2.me/theorems/2a6734ec-769e-40a1-bbca-5bc3747a4e85
-- title:
--   §2, p. 95 — (PR_λ) separates into one binary knapsack per agent
-- statement:
--   Fix multipliers $\lambda_j$. For every $x$ the objective of (PR$_\lambda$) can be written
--
--   $$
--   \sum_{i\in I}\sum_{j\in J}c_{ij}x_{ij}+\sum_{j\in J}\lambda_j\Bigl(1-\sum_{i\in I}x_{ij}\Bigr)=\sum_{j\in J}\lambda_j-\sum_{i\in I}\sum_{j\in J}(\lambda_j-c_{ij})x_{ij}.
--   $$
--
--   Moreover, a point $x$ feasible for (PR$_\lambda$) is optimal for (PR$_\lambda$) if and only if, for every agent $i$, the row $(x_{ij})_{j\in J}$ is optimal for agent $i$'s binary knapsack problem
--
--   $$
--   \max\ \sum_{j\in J}(\lambda_j-c_{ij})v_j\quad\text{s.t.}\quad \sum_{j\in J}r_{ij}v_j\le b_i,\quad v_j\in\{0,1\}.
--   $$
--
--   So the optimal value of (PR$_\lambda$) is $\sum_j\lambda_j$ minus the sum over agents of their knapsack optima: (PR$_\lambda$) separates into a series of binary knapsack problems, one for each $i\in I$.
--
--   **Formalization Note** The paper writes the "equivalent form of the objective function" as $\sum_j\lambda_j-\max[\sum_j\sum_i(\lambda_j-c_{ij})x_{ij}]$; the $\max$ belongs to the optimal value, not to the objective of a single point. The statement gives the pointwise identity and the separation of optimal solutions, which together give the optimal-value form.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 95, §2, the display after (PR_λ) and the sentence 'Thus (PR_λ) separates into a series of binary knapsack problems, one for each i ∈ I.'

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem lagrangean_separates_into_knapsacks {m n : ℕ} (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (lam : Fin n → ℝ) :
    (∀ x, lagObj c lam x = ∑ j, lam j - ∑ i, knapObj c lam i (x i)) ∧
    ∀ x, FeasibleLag r b x →
      ((∀ x', FeasibleLag r b x' → lagObj c lam x ≤ lagObj c lam x') ↔
        ∀ i v, KnapFeasible r b i v → knapObj c lam i v ≤ knapObj c lam i (x i)) := by sorry

end RossSolandGAP.Bound
