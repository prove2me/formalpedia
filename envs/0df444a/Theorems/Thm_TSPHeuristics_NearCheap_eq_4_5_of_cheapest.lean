-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_eq_4_5_of_cheapest
-- name    : TSPHeuristics.NearCheap.eq_4_5_of_cheapest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:58:25.536985+00:00
-- url     : https://prove2.me/theorems/d75ed720-ca62-4566-a84b-e04499921882
-- title:
--   Proof of Theorem 4 — cheapest insertion satisfies (4.5): COST(T_i, a_i) ≤ 2·d(p, q)
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n$ nodes and let $T_1, \dots, T_n$, $a_0, \dots, a_{n-1}$ be a run of **cheapest insertion**: an insertion method in which each $a_i$ ($1 \le i < n$) minimizes $\mathrm{COST}(T_i, x)$ over all nodes $x \notin T_i$. Then for every $1 \le i < n$, every node $p \in T_i$ and every node $q \notin T_i$,
--
--   $$
--   \mathrm{COST}(T_i, a_i) \le 2\, d(p,q). \qquad (4.5)
--   $$
--
--   This is the hypothesis of Lemma 3, established for cheapest insertion, so that Lemma 3 applies to both heuristics.
--
--   **Formalization Note** The start node $a_0$ and all ties are arbitrary. The distance satisfies $d(i,i)=0$ (normalization).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 574, proof of Theorem 4, the two sentences after (4.10) (cheapest insertion satisfies (4.5))

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem eq_4_5_of_cheapest {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (hrule : TSPHeuristics.Shared.IsCheapestRule d T a) :
    ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      TSPHeuristics.Shared.insCost d (T i) (a i) ≤ 2 * d p q := by sorry

end TSPHeuristics.NearCheap
