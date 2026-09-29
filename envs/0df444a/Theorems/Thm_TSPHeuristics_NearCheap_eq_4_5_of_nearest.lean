-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_eq_4_5_of_nearest
-- name    : TSPHeuristics.NearCheap.eq_4_5_of_nearest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:57:55.709853+00:00
-- url     : https://prove2.me/theorems/6ef8b9b6-b8a9-4a29-9c75-a0d9a2881e62
-- title:
--   Eqs. (4.9)–(4.10) — nearest insertion satisfies (4.5): COST(T_i, a_i) ≤ 2·d(p, q)
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n$ nodes and let $T_1, \dots, T_n$, $a_0, \dots, a_{n-1}$ be a run of **nearest insertion**: an insertion method in which each $a_i$ ($1 \le i < n$) minimizes the distance $d(T_i, x) = \min_{y \in T_i} d(y, x)$ over all nodes $x \notin T_i$. Then for every $1 \le i < n$, every node $p \in T_i$ and every node $q \notin T_i$,
--
--   $$
--   \mathrm{COST}(T_i, a_i) \le 2\, d(p,q). \qquad (4.5)
--   $$
--
--   This is the hypothesis of Lemma 3, established for nearest insertion; together with Lemma 3 it bounds the nearest-insertion tour by twice a minimal spanning tree.
--
--   **Formalization Note** The start node $a_0$ and the resolution of ties among nearest nodes and among cheapest insertion positions are arbitrary. The distance satisfies $d(i,i)=0$ (normalization).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 574, proof of Theorem 4, eqs. (4.9), (4.10), yielding (4.5) for nearest insertion

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem eq_4_5_of_nearest {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (hrule : TSPHeuristics.Shared.IsNearestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      TSPHeuristics.Shared.insCost d (T i) (a i) ≤ 2 * d p q := by sorry

end TSPHeuristics.NearCheap
