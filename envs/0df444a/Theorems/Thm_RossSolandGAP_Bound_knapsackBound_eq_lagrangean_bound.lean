-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_knapsackBound_eq_lagrangean_bound
-- name    : RossSolandGAP.Bound.knapsackBound_eq_lagrangean_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:12:24.970852+00:00
-- url     : https://prove2.me/theorems/bfcd605e-dba6-408e-a200-648229b7ad6e
-- title:
--   §2, p. 96 — the knapsack bound LB equals the optimal value of (PR_λ) at λ_j = c_2j, and is a lower bound for (P)
-- statement:
--   Consider the generalized assignment problem (P) with $m\ge2$ agents, $n$ tasks, real costs $c_{ij}$, resources $r_{ij}\ge0$ and budgets $b_i>0$. Choose for every task $j$ a cheapest agent $i_j$, $c_{i_jj}=\min_ic_{ij}$, let $Z=\sum_jc_{i_jj}$ be the value of the relaxation (PR), let $J_i=\{j:i_j=i\}$, $I'=\{i:\sum_{j\in J_i}r_{ij}>b_i\}$, and for each $i\in I'$ let $y^*_i$ be an optimal solution of the binary knapsack problem
--
--   $$
--   \text{(PK}_i)\qquad\min\ z_i=\sum_{j\in J_i}p_jy_{ij}\quad\text{s.t.}\quad\sum_{j\in J_i}r_{ij}y_{ij}\ge d_i,\ y_{ij}\in\{0,1\},
--   $$
--
--   with $d_i=\sum_{j\in J_i}r_{ij}-b_i$, $p_j=\min_{k\ne i_j}(c_{kj}-c_{i_jj})$, and optimal value $z^*_i$. Let $\mathrm{LB}=Z+\sum_{i\in I'}z^*_i$, and let $c_{2j}$ be the second smallest of $c_{1j},\dots,c_{mj}$. Write $L_{c_2}(x)=\sum_i\sum_jc_{ij}x_{ij}+\sum_jc_{2j}(1-\sum_ix_{ij})$ for the objective of the Lagrangean relaxation (PR$_\lambda$) at $\lambda=c_2$, whose feasible points are the binary $x$ with $\sum_jr_{ij}x_{ij}\le b_i$ for all $i$. Then
--
--   1. $\mathrm{LB}\le L_{c_2}(x)$ for every $x$ feasible for (PR$_\lambda$);
--   2. $\mathrm{LB}=L_{c_2}(x)$ for some $x$ feasible for (PR$_\lambda$);
--   3. $\mathrm{LB}\le\sum_i\sum_jc_{ij}x_{ij}$ for every $x$ feasible for (P).
--
--   Items 1 and 2 say that
--
--   $$
--   \mathrm{LB}=\min\bigl\{L_{c_2}(x) : x\ \text{feasible for (PR}_\lambda)\bigr\},
--   $$
--
--   the paper's principal result: the lower bound LB "is identical to the bound provided by (PR$_\lambda$) when each $\lambda_j$ is set equal to $c_{2j}$". Item 3 is its consequence, "which is clearly a valid bound for (P)".
--
--   The result identifies the cheap knapsack-penalty bound, computed from one (PR) solution and one small knapsack per overloaded agent, with a Lagrangean dual bound. This is what makes the bound valid and what places the algorithm in the Lagrangean-relaxation framework.
--
--   **Formalization Note** Agents and tasks are 0-based (`Fin m`, `Fin n`). $r_{ij}\ge0$ is implicit in the paper ("the resource required") and is necessary: with a negative $r_{ij}$ a task could be put on a second agent to free budget, and both (PR$_\lambda$) and (P) can go below LB. $m\ge2$ is needed for $p_j$ and $c_{2j}$ to exist. $b_i>0$ is printed on p. 92. The cheapest selection $i_j$ is any function with `IsCheapest c a`, so the statement holds for every tie-break, and $y^*_i$ is any optimal solution of (PK$_i$), $i\in I'$ (its values outside $J_i$ and for $i\notin I'$ are ignored). The (PR$_\lambda$) competitors in item 1 are all binary points within the budgets, with any number of agents per task.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 96, §2, second paragraph ('The principal result of this Lagrangean analysis ...')

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem knapsackBound_eq_lagrangean_bound {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hb : ∀ i, 0 < b i) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin n → Fin m) (ha : IsCheapest c a) (ystar : Fin m → Fin n → ℝ)
    (hystar : ∀ i ∈ Iprime r b a, IsOptPK hm c r b a i (ystar i)) :
    (∀ x, FeasibleLag r b x → LB hm c r b a ystar ≤ lagObj c (c2 hm c a) x) ∧
    (∃ x, FeasibleLag r b x ∧ lagObj c (c2 hm c a) x = LB hm c r b a ystar) ∧
    (∀ x, FeasibleP r b x → LB hm c r b a ystar ≤ cost c x) := by sorry

end RossSolandGAP.Bound
