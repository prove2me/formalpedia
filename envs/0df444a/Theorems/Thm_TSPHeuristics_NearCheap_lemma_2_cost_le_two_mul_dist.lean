-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_lemma_2_cost_le_two_mul_dist
-- name    : TSPHeuristics.NearCheap.lemma_2_cost_le_two_mul_dist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:56:42.881498+00:00
-- url     : https://prove2.me/theorems/76218bae-fada-4e17-a75b-97bcd578d78c
-- title:
--   Lemma 2 — inserting k costs at most twice its distance to any node of the subtour
-- statement:
--   Let $(N, d)$ be a traveling salesman graph, $T$ a subtour (a nonempty list of distinct nodes), $k$ a node not in $T$, and $j$ a node in $T$. Then
--
--   $$
--   \mathrm{COST}(T,k) \le 2\, d(k,j). \qquad (3.3)
--   $$
--
--   Here $\mathrm{COST}(T,k)$ is the increase in length when $k$ is inserted into $T$ at a cheapest position. The lemma is the basic consequence of the triangle inequality on which every bound for insertion methods rests.
--
--   **Formalization Note** The distance satisfies $d(i,i) = 0$ in addition to the paper's axioms (a normalization, see the definition `Model`).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 571, Lemma 2, eq. (3.3)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem lemma_2_cost_le_two_mul_dist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : List (Fin n)) (hT : T.Nodup) (hTne : T ≠ []) (k j : Fin n) (hk : k ∉ T) (hj : j ∈ T) :
    TSPHeuristics.Shared.insCost d T k ≤ 2 * d k j := by sorry

end TSPHeuristics.NearCheap
