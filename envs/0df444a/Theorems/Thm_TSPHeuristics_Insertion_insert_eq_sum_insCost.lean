-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_insert_eq_sum_insCost
-- name    : TSPHeuristics.Insertion.insert_eq_sum_insCost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:34:06.853984+00:00
-- url     : https://prove2.me/theorems/e9c1561e-0f7d-457f-8d9b-5d8cb66d6bab
-- title:
--   Eq. (3.7) — INSERT = Σ_{i=1}^{n−1} COST(T_i, a_i)
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n\ge1$ nodes, and let $T_1,\dots,T_n$ and $a_0,\dots,a_{n-1}$ be the subtours and nodes of an insertion method run. Then the length INSERT of the final tour $T_n$ is the sum of the insertion costs:
--   $$\mathrm{INSERT}=\sum_{i=1}^{n-1}\mathrm{COST}(T_i,a_i).\tag{3.7}$$
--
--   This bookkeeping identity turns the bound on INSERT into a bound on a sum of per-node quantities, to which Lemma 1 applies.
--
--   **Formalization Note** Subtours are lists of nodes; the closed length of a list $[x_0,\dots,x_{m-1}]$ is $d(x_0,x_1)+\dots+d(x_{m-2},x_{m-1})+d(x_{m-1},x_0)$. The paper's 1-based subtour index is kept: $T_1=[a_0]$, and $T_n$ is the final tour. Every choice of the inserted nodes and every minimizing insertion position is allowed. $d(i,i)=0$ is assumed as a normalization (not in the paper; it never enters a length).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 571, proof of Theorem 3, eq. (3.7)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.7), p. 571: the length of the tour `T n` built by an insertion method is the sum of the
insertion costs, `INSERT = Σ_{i=1}^{n-1} COST(T_i, a_i)`. -/
theorem insert_eq_sum_insCost {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by sorry

end TSPHeuristics.Insertion
