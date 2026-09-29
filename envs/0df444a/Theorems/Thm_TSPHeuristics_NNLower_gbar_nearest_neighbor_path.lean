-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_gbar_nearest_neighbor_path
-- name    : TSPHeuristics.NNLower.gbar_nearest_neighbor_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:27:08.807817+00:00
-- url     : https://prove2.me/theorems/5032951e-67a0-40fc-83f6-8b6b98dfcb1e
-- title:
--   Property b): nearest neighbor from the start node can produce $P_i$
-- statement:
--   For every $i\ge1$, the nearest neighbor algorithm on $\bar G_i$, started at the start node of $G_i$, can, with a suitable resolution of ties, visit the nodes in the order of the path $P_i$ and then return from the middle node (the last node of $P_i$) to the start node. That is, the tour $\tau$ with $\tau(k)=$ the $k$-th node of $P_i$ ($k=0,\dots,2^{i+1}-2$) exists and is a nearest-neighbor tour of $\bar G_i$.
--
--   This is property b) of p. 568: it identifies one run of the algorithm whose tour is long.
--
--   **Formalization Note** "The $k$-th node of $P_i$" is `(pathP i).getD k 0`; the statement asserts that some permutation lists $P_i$ (so $P_i$ visits every node once) and that it satisfies `IsNearestNeighborTour`, which allows ties to be broken arbitrarily.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 568, property b)

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- Property b), p. 568: for `i ≥ 1`, the nearest neighbor method started at the start node of
`Ḡ_i` can (with suitable resolution of ties) produce the path `P_i` followed by the edge returning
from the middle node to the start node: the tour that visits the nodes in the order of `P_i` is a
nearest-neighbor tour of `Ḡ_i`. -/
theorem gbar_nearest_neighbor_path (i : ℕ) (hi : 1 ≤ i) :
    ∃ τ : Equiv.Perm (Fin (numNodes i)),
      (∀ k : Fin (numNodes i), (τ k : ℕ) = (pathP i).getD k 0) ∧
      IsNearestNeighborTour (gbar i) τ := by sorry

end TSPHeuristics.NNLower
