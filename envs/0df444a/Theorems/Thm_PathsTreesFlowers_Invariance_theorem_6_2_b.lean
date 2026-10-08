-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_theorem_6_2_b
-- name    : PathsTreesFlowers.Invariance.theorem_6_2_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:56.531232+00:00
-- url     : https://prove2.me/theorems/c0ce192c-cce6-43c6-ae40-5692932322b9
-- title:
--   6.2 (b), p. 464 — the inner vertices I(G) are precisely the vertices not in O(G) but joined to vertices in O(G)
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^*$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ and inner vertices $I(G)$ as in 6.2. Then for every vertex $v$ of $G$,
--   $$v \in I(G) \iff v \notin O(G) \text{ and } v \text{ is joined by an edge of } G \text{ to a vertex of } O(G).$$
--
--   Since $O(G)$ is characterized by 6.2 (a) without reference to the construction, this shows that $I(G)$ too depends on $G$ alone.
--
--   **Formalization Note** The configuration is the structure `Config60`; $O(G)$ and $I(G)$ are `outerSet` and `innerSet`.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 464, 6.2 (b); proof in 6.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.2 (b), p. 464: the inner vertices `I(G)` are precisely the vertices of `G` not in `O(G)`
but joined to vertices in `O(G)`. -/
theorem theorem_6_2_b {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ v : V, v ∈ innerSet C ↔ v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v) := by sorry

end PathsTreesFlowers.Invariance
