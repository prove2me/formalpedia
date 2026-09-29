-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_rebuilt_solution_cost
-- name    : RossSolandGAP.Bound.rebuilt_solution_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:12:49.380978+00:00
-- url     : https://prove2.me/theorems/c0ee42b0-0f25-47c4-b33e-2a9656ff7ee3
-- title:
--   §2, pp. 94–95 — the solution rebuilt from the y*_ij has objective value LB
-- statement:
--   Assume the setting of the principal result: $m\ge2$, $b_i>0$, $r_{ij}\ge0$, a cheapest-agent selection $j\mapsto i_j$, and optimal solutions $y^*_i$ of (PK$_i$) for $i\in I'$. For every task $j$ let $k_j\ne i_j$ be an agent with $p_j=c_{k_jj}-c_{i_jj}$. Build $x'$ from the (PR) solution: every task $j$ with $i_j\in I'$ and $y^*_{i_jj}=1$ is taken from $i_j$ ($x'_{i_jj}=0$) and given to $k_j$ ($x'_{k_jj}=1$); every other task stays with $i_j$. Then $x'$ is feasible for (PR) and
--
--   $$
--   \sum_{i\in I}\sum_{j\in J}c_{ij}x'_{ij}=\mathrm{LB}.
--   $$
--
--   Consequently, if $x'$ also satisfies the resource constraints, i.e. is feasible for (P), it is an optimal solution of (P).
--
--   The construction is how the algorithm finds candidate incumbents: the knapsack solutions say which tasks to move, and the move costs exactly the penalty.
--
--   **Formalization Note** The optimality conclusion combines the cost identity with the principal result, so it carries the same hypotheses ($r_{ij}\ge0$, $b_i>0$, $m\ge2$). Agents and tasks are 0-based.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, pp. 94-95, §2, paragraph after the display LB

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem rebuilt_solution_cost {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 < b i) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin n → Fin m) (ha : IsCheapest c a) (ystar : Fin m → Fin n → ℝ)
    (hystar : ∀ i ∈ Iprime r b a, IsOptPK hm c r b a i (ystar i))
    (k : Fin n → Fin m) (hk : ∀ j, k j ≠ a j ∧ pen hm c a j = c (k j) j - c (a j) j) :
    FeasiblePR (rebuilt r b a ystar k) ∧
    cost c (rebuilt r b a ystar k) = LB hm c r b a ystar ∧
    (FeasibleP r b (rebuilt r b a ystar k) →
      ∀ x, FeasibleP r b x → cost c (rebuilt r b a ystar k) ≤ cost c x) := by sorry

end RossSolandGAP.Bound
