-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_lemma_2_insCost_le_two_mul_dist
-- name    : TSPHeuristics.Insertion.lemma_2_insCost_le_two_mul_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:33:36.970072+00:00
-- url     : https://prove2.me/theorems/f783afb2-16fe-4ce1-87a3-ae9eacf85603
-- title:
--   Lemma 2 — COST(T, k) ≤ 2·d(k, j) for every node j of T
-- statement:
--   Let $(N,d)$ be a traveling salesman graph, $T$ a subtour, $k$ a node not in $T$ and $j$ a node in $T$. Then
--   $$\mathrm{COST}(T,k)\ \le\ 2\,d(k,j).\tag{3.3}$$
--
--   Inserting a node never costs more than going to any node already on the subtour and back. The lemma drives both the logarithmic bound for every insertion method (Theorem 3) and the constant-factor bounds for nearest and cheapest insertion.
--
--   **Formalization Note** Subtours are lists of nodes; the closed length of a list $[x_0,\dots,x_{m-1}]$ is $d(x_0,x_1)+\dots+d(x_{m-2},x_{m-1})+d(x_{m-1},x_0)$. The paper's 1-based subtour index is kept: $T_1=[a_0]$, and $T_n$ is the final tour. Every choice of the inserted nodes and every minimizing insertion position is allowed. $d(i,i)=0$ is assumed as a normalization (not in the paper; it never enters a length). A subtour is a list without repeated nodes.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 571, Lemma 2, eq. (3.3)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Lemma 2, p. 571, (3.3): for a subtour `T`, a node `k` not in `T` and a node `j` in `T`,
`COST(T, k) ≤ 2 · d(k, j)`. -/
theorem lemma_2_insCost_le_two_mul_dist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (hT : T.Nodup) (k j : Fin n) (hk : k ∉ T) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by sorry

end TSPHeuristics.Insertion
