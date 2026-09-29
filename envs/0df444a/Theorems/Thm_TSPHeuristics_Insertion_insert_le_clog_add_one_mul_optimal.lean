-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_insert_le_clog_add_one_mul_optimal
-- name    : TSPHeuristics.Insertion.insert_le_clog_add_one_mul_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:35:40.528819+00:00
-- url     : https://prove2.me/theorems/17e06697-1d83-43e4-a993-febc46977b58
-- title:
--   Theorem 3 — every insertion method gives INSERT ≤ (⌈lg n⌉ + 1)·OPTIMAL
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n\ge1$ nodes (symmetric, nonnegative distances satisfying the triangle inequality). Let $T_1,\dots,T_n$ be the subtours of any insertion method: $T_1$ is a single node $a_0$, and each $T_{i+1}$ is obtained from $T_i$ by inserting some node $a_i\notin T_i$ at a position that minimizes the increase in length. Let INSERT be the length of the final tour $T_n$ and OPTIMAL the length of a shortest tour. Then
--   $$\mathrm{INSERT}\ \le\ \bigl(\lceil\lg n\rceil+1\bigr)\,\mathrm{OPTIMAL}.\tag{3.6}$$
--
--   The bound holds regardless of how the nodes $a_i$ are selected and how ties between insertion positions are broken. It places every insertion heuristic (nearest, cheapest, farthest, random, arbitrary insertion) within a logarithmic factor of optimal.
--
--   **Formalization Note** Subtours are lists of nodes; the closed length of a list $[x_0,\dots,x_{m-1}]$ is $d(x_0,x_1)+\dots+d(x_{m-2},x_{m-1})+d(x_{m-1},x_0)$. The paper's 1-based subtour index is kept: $T_1=[a_0]$, and $T_n$ is the final tour. Every choice of the inserted nodes and every minimizing insertion position is allowed. $d(i,i)=0$ is assumed as a normalization (not in the paper; it never enters a length). The paper's ratio $\mathrm{INSERT}/\mathrm{OPTIMAL}\le\lceil\lg n\rceil+1$ is stated multiplied out, so the case OPTIMAL $=0$ (which the paper excludes by (1.1)) needs no separate hypothesis. $\lceil\lg n\rceil$ is `Nat.clog 2 n`.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 571, Theorem 3, eq. (3.6)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Theorem 3, (3.6), p. 571: for a traveling salesman graph with `n` nodes, every tour
produced by an insertion method (any choice of the inserted nodes, any minimizing insertion
position) has length `INSERT ≤ (⌈lg n⌉ + 1) · OPTIMAL`. -/
theorem insert_le_clog_add_one_mul_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
