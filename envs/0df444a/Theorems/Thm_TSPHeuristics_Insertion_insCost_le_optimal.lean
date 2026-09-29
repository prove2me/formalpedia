-- Prove2me | Theorems.Thm_TSPHeuristics_Insertion_insCost_le_optimal
-- name    : TSPHeuristics.Insertion.insCost_le_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:35:13.267648+00:00
-- url     : https://prove2.me/theorems/b7e8a085-bb43-4af5-a46e-c39a7aca414b
-- title:
--   Eq. (3.12) — COST(T_i, a_i) ≤ OPTIMAL
-- statement:
--   Let $(N,d)$ be a traveling salesman graph with $n$ nodes, and let $T_1,\dots,T_n$ and $a_0,\dots,a_{n-1}$ be the subtours and nodes of an insertion method run. For every $1\le i<n$,
--   $$\mathrm{COST}(T_i,a_i)\ \le\ \mathrm{OPTIMAL}.\tag{3.12}$$
--
--   With $l_{a_i}=\tfrac12\mathrm{COST}(T_i,a_i)$ this is condition b) of Lemma 1.
--
--   **Formalization Note** Subtours are lists of nodes; the closed length of a list $[x_0,\dots,x_{m-1}]$ is $d(x_0,x_1)+\dots+d(x_{m-2},x_{m-1})+d(x_{m-1},x_0)$. The paper's 1-based subtour index is kept: $T_1=[a_0]$, and $T_n$ is the final tour. Every choice of the inserted nodes and every minimizing insertion position is allowed. $d(i,i)=0$ is assumed as a normalization (not in the paper; it never enters a length).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 572, proof of Theorem 3, eqs. (3.12)–(3.13)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (3.12), p. 572: in an insertion method run, every insertion cost is at most OPTIMAL:
`COST(T_i, a_i) ≤ OPTIMAL` for `1 ≤ i < n`. -/
theorem insCost_le_optimal {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    ∀ i : ℕ, 1 ≤ i → i < n → insCost d (T i) (a i) ≤ TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
