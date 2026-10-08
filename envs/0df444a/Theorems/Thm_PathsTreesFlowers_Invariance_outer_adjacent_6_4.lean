-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_outer_adjacent_6_4
-- name    : PathsTreesFlowers.Invariance.outer_adjacent_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:36.246425+00:00
-- url     : https://prove2.me/theorems/79220a60-8b4a-4e20-a27a-c724ca09b004
-- title:
--   6.4, p. 464 — each outer vertex of G is joined only to inner vertices and to its own expansion; each inner vertex is joined to an outer vertex
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^* = G/\mathcal P$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ and inner vertices $I(G)$ as in 6.2. Then:
--
--   1. every outer vertex $u$ of $G$ is joined only to inner vertices and to other vertices in the complete expansion of its image $u^*$: if an edge of $G$ joins $u \in O(G)$ to $w$, then
--   $$w \in I(G) \quad\text{or}\quad w \text{ lies in the same part of } \mathcal P \text{ as } u;$$
--   2. every inner vertex of $G$ is joined by an edge of $G$ to an outer vertex of $G$.
--
--   These two facts give 6.2 (b) directly, and together with the connectedness of the complete expansions they give 6.2 (c).
--
--   **Formalization Note** The configuration $(G^*, \{J_i\})$ is the structure `Config60`, which records all invariants of construction 6.0, including that each $J_i$ is Hungarian in $G^* - J_1 - \dots - J_{i-1}$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 464, 6.4 (first paragraph)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.4, p. 464: each outer vertex `u` of `G` is joined only to inner vertices and to other
vertices in the complete expansion of its image `u*`; and each inner vertex is joined to an outer
vertex of `G`. -/
theorem outer_adjacent_6_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    (∀ u ∈ outerSet C, ∀ (e : E) (w : V), G.ends e = s(u, w) →
      w ∈ innerSet C ∨ C.P.part w = C.P.part u) ∧
    (∀ v ∈ innerSet C, ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v)) := by sorry

end PathsTreesFlowers.Invariance
