-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_exposed_only_outer_6_6
-- name    : PathsTreesFlowers.Invariance.exposed_only_outer_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:02.805396+00:00
-- url     : https://prove2.me/theorems/5f547165-1577-4e30-ad07-f491462e46e1
-- title:
--   6.6, p. 465 — only the outer vertices are ever exposed for a maximum matching (converse half of 6.2 (a))
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^*$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ as in 6.2. Then every vertex left exposed by some maximum matching of $G$ is an outer vertex:
--   $$\forall M' \text{ maximum matching of } G,\ \forall v \text{ exposed for } M':\quad v \in O(G).$$
--
--   Together with 6.5 this is 6.2 (a).
--
--   **Formalization Note** The configuration is the structure `Config60`; $O(G)$ is `outerSet`.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 465, 6.6 (first sentence and last paragraph)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.6, p. 465: only the outer vertices are ever exposed for a maximum matching (the converse
half of 6.2 (a)). -/
theorem exposed_only_outer_6_6 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ (M' : Finset E) (v : V), PathsTreesFlowers.Duality.IsMaxMatching G M' → PathsTreesFlowers.Duality.IsExposed G M' v → v ∈ outerSet C := by sorry

end PathsTreesFlowers.Invariance
