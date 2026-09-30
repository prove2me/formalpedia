-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_cheapest_assignment_solves_PR
-- name    : RossSolandGAP.Bound.cheapest_assignment_solves_PR
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:08:36.942349+00:00
-- url     : https://prove2.me/theorems/bcaa19ab-c943-49d4-acd3-908912df6fc1
-- title:
--   §2, pp. 93–94 — assigning each task to a least-cost agent solves (PR), with value $Z$
-- statement:
--   Consider the relaxation (PR) of the generalized assignment problem: minimize $\sum_{i\in I}\sum_{j\in J}c_{ij}x_{ij}$ subject to $\sum_{i\in I}x_{ij}=1$ for all $j$ and $x_{ij}\in\{0,1\}$. Choose for every task $j$ an agent $i_j$ with $c_{i_j j}=\min_{i\in I}c_{ij}$, and let $\bar x_{i_j j}=1$, $\bar x_{ij}=0$ for $i\ne i_j$. Then $\bar x$ is feasible for (PR), its cost is
--
--   $$
--   Z=\sum_{j\in J}c_{i_j j},
--   $$
--
--   and $Z\le\sum_i\sum_j c_{ij}x_{ij}$ for every $x$ feasible for (PR). Consequently $Z\le\sum_i\sum_j c_{ij}x_{ij}$ for every $x$ feasible for (P), whatever the resources $r_{ij}$ and budgets $b_i$.
--
--   This is the starting bound of the algorithm; the knapsack penalties are added to it.
--
--   **Formalization Note** The selection $j\mapsto i_j$ is any function with `IsCheapest c a`; ties are allowed. The last conjunct ("$Z$ is a lower bound for (P)") is the paper's "This yields the lower bound", made explicit. Agents and tasks are 0-based (`Fin m`, `Fin n`).
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, pp. 93-94, §2, last paragraph of p. 93 and the display Z on p. 94

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem cheapest_assignment_solves_PR {m n : ℕ} (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m)
    (ha : IsCheapest c a) :
    FeasiblePR (xPR a) ∧ cost c (xPR a) = Z c a ∧
    (∀ x, FeasiblePR x → Z c a ≤ cost c x) ∧
    (∀ (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin m → Fin n → ℝ),
      FeasibleP r b x → Z c a ≤ cost c x) := by sorry

end RossSolandGAP.Bound
