-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_weak_duality
-- name    : PathsTreesFlowers.Duality.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:14.291008+00:00
-- url     : https://prove2.me/theorems/561ef049-c24b-4a30-a3a6-6246a9a664df
-- title:
--   5.6, proof, first paragraph, p. 463 — weak duality: |M| ≤ capacity-sum of any odd-set cover
-- statement:
--   Let $G$ be a finite graph, $M$ a matching of $G$ and $\mathcal S$ an odd-set cover of $G$. Then
--
--   $$|M| \le \operatorname{cap}(\mathcal S) = \sum_{U \in \mathcal S} \operatorname{cap}(U).$$
--
--   This is the easy half of the matching-duality theorem: the capacity-sum of any odd-set cover is at least the cardinality of any matching, so equality certifies that both are optimal.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 463, 5.6, proof, first paragraph

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

namespace PathsTreesFlowers.Duality

theorem weak_duality {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (S : Finset (Finset V))
    (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (hS : IsOddSetCover G S) :
    M.card ≤ capacitySum S := by sorry

end PathsTreesFlowers.Duality
