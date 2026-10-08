-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_outer_exposed_6_5
-- name    : PathsTreesFlowers.Invariance.outer_exposed_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:06.852517+00:00
-- url     : https://prove2.me/theorems/e8a07e8c-01c8-48c6-8ee5-9e3cb7481d5c
-- title:
--   6.5, pp. 464–465 — every outer vertex of G is left exposed by some maximum matching of G (half of 6.2 (a))
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^*$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ as in 6.2. Then every outer vertex of $G$ is exposed for some maximum matching:
--   $$\forall v \in O(G)\ \ \exists M' \text{ a maximum matching of } G \text{ with } v \text{ exposed for } M'.$$
--
--   This is one half of 6.2 (a); the converse is 6.6.
--
--   **Formalization Note** The configuration is the structure `Config60`; $O(G)$ is `outerSet`.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), pp. 464–465, 6.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.5, pp. 464–465: every outer vertex of `G` is left exposed by some maximum matching of `G`
(half of 6.2 (a)). -/
theorem outer_exposed_6_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v ∈ outerSet C, ∃ M' : Finset E, PathsTreesFlowers.Duality.IsMaxMatching G M' ∧ PathsTreesFlowers.Duality.IsExposed G M' v := by sorry

end PathsTreesFlowers.Invariance
