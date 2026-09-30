-- Prove2me | Theorems.Thm_SupplyChainTheory_nearest_insertion_bound
-- name    : SupplyChainTheory.nearest_insertion_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:56:33.865254+00:00
-- url     : https://prove2.me/theorems/997a7052-3472-4e2c-8565-066d2f9d9f3b
-- title:
--   Theorem 10.7: the nearest insertion tour satisfies $z_{NI}/z^* \le 2$
-- statement:
--   **Theorem 10.7.** For every instance of the TSP that satisfies the triangle inequality,
--
--   $$ \frac{z_{NI}}{z^*} \;\le\; 2, $$
--
--   where $z^*$ and $z_{NI}$ are the lengths of the optimal tour and of the nearest-insertion tour:
--   starting from a single node, repeatedly insert the unvisited node nearest to the current tour at
--   the position that increases the tour length least (Algorithm 10.2). The book omits the proof
--   and cites Rosenkrantz et al.; their argument charges each insertion to an edge of the minimum
--   spanning tree built by Prim's algorithm in the same order, so the tour costs at most twice the
--   tree, and Lemma 10.9 bounds the tree by $z^*$. Theorem 10.8 shows the bound of $2$ is tight.
--
--   **Formalization Note** A run is any sequence of partial tours obeying the two selection rules,
--   so every tie-breaking is covered; the final list is the $n$-th partial tour and its closed length
--   is compared with $z^*$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 420, Sect. 10.4.2, Theorem 10.7, Eq. (10.26): 'Proof. Omitted; see Rosenkrantz et al. (1977)'; Algorithm 10.2

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem nearest_insertion_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (L : ℕ → List (Fin n)) (hL : IsNearestInsertionRun c L) :
    cycleLength c (L (n - 1)) ≤ 2 * optTourLength c := by sorry

end SupplyChainTheory
