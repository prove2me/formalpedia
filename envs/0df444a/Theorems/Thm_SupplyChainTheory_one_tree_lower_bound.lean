-- Prove2me | Theorems.Thm_SupplyChainTheory_one_tree_lower_bound
-- name    : SupplyChainTheory.one_tree_lower_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:59:16.846175+00:00
-- url     : https://prove2.me/theorems/acfc89e5-d482-412c-b1ec-a37529665ae8
-- title:
--   Lemma 10.15: the optimal 1-tree is a lower bound, $z(\hat T^*) \le z^*$
-- statement:
--   **Lemma 10.15.** Let $\hat T^*$ be an optimal 1-tree for a TSP instance on $n \ge 3$ nodes, a
--   spanning tree on the nodes other than the root plus two edges incident to the root, of least
--   total length. Then $z(\hat T^*) \le z^*$.
--
--   Every tour is a 1-tree: removing the root leaves a spanning path on the other nodes, and the
--   root has degree two. So the minimum 1-tree is a relaxation of the TSP, one that is easy to
--   compute (an MST on the other nodes plus the two shortest edges at the root) and that improves on
--   the MST bound by one edge.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 442, Sect. 10.6.1, Lemma 10.15; after Held and Karp (1970)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem one_tree_lower_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (r : Fin n) : opt1TreeLength c r ≤ optTourLength c := by sorry

end SupplyChainTheory
