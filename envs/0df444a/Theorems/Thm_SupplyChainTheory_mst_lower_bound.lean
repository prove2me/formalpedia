-- Prove2me | Theorems.Thm_SupplyChainTheory_mst_lower_bound
-- name    : SupplyChainTheory.mst_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:57:03.433438+00:00
-- url     : https://prove2.me/theorems/a8e6daae-b49f-4de9-906b-7dd68fcda952
-- title:
--   Lemma 10.9: the minimum spanning tree is a lower bound, $z(T^*) \le z^*$
-- statement:
--   **Lemma 10.9.** Let $T^*$ be a minimum spanning tree on the nodes of a TSP instance satisfying
--   the triangle inequality. Then $z(T^*) \le z^*$: the total length of the tree is at most the length
--   of the optimal tour.
--
--   Removing any edge from the optimal tour leaves a spanning path, which is a spanning tree of
--   length at most $z^*$ (the removed edge has nonnegative length), and the minimum spanning tree is
--   no longer than that path. The lemma is the source of the MST-based heuristics and of the
--   Held-Karp bound.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 430-431, Sect. 10.4.6, Lemma 10.9 and its proof

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem mst_lower_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) : graphWeight c T ≤ optTourLength c := by sorry

end SupplyChainTheory
