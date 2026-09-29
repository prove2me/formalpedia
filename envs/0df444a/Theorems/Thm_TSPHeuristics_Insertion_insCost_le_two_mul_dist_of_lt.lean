-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_insCost_le_two_mul_dist_of_lt
-- name    : TSPHeuristics.Insertion.insCost_le_two_mul_dist_of_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:34:37.567+00:00
-- url     : https://prove2.me/theorems/8716059a-341a-48e3-abc2-127ea98d18b3
-- title:
--   Eq. (3.10) — COST(T_i, a_i) ≤ 2·d(a_i, a_j) for j < i
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n$ nodes, and let $T_1,\dots,T_n$ and $a_0,\dots,a_{n-1}$ be the subtours and nodes of an insertion method run. For all indices $0\le j<i<n$,
--   $$\mathrm{COST}(T_i,a_i)\ \le\ 2\,d(a_i,a_j).\tag{3.10}$$
--
--   The node $a_j$ already lies on $T_i$ when $a_i$ is inserted, so this is Lemma 2 applied along the run. With $l_{a_i}=\tfrac12\mathrm{COST}(T_i,a_i)$ and $l_{a_0}=0$ it gives condition a) of Lemma 1.
--
--   **Formalization Note** Subtours are lists of nodes; the closed length of a list $[x_0,\dots,x_{m-1}]$ is $d(x_0,x_1)+\dots+d(x_{m-2},x_{m-1})+d(x_{m-1},x_0)$. The paper's 1-based subtour index is kept: $T_1=[a_0]$, and $T_n$ is the final tour. Every choice of the inserted nodes and every minimizing insertion position is allowed. $d(i,i)=0$ is assumed as a normalization (not in the paper; it never enters a length).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 572, proof of Theorem 3, eqs. (3.8)–(3.11)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.10), p. 572: in an insertion method run, for `j < i < n` (so `a_j` already lies in
`T_i` when `a_i` is inserted), `COST(T_i, a_i) ≤ 2 · d(a_i, a_j)`. -/
theorem insCost_le_two_mul_dist_of_lt {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i j : ℕ, j < i → i < n → insCost d (T i) (a i) ≤ 2 * d (a i) (a j) := by sorry

end TSPHeuristics.Insertion
