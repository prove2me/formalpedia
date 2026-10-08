-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_exists_hungarian_tree_5_8
-- name    : PathsTreesFlowers.Duality.exists_hungarian_tree_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:48:41.264371+00:00
-- url     : https://prove2.me/theorems/9fec91ae-5b72-4550-a8e9-f0fb79a7cbc7
-- title:
--   5.8, first sentence, p. 463 — the algorithm applied to a maximum matching from an exposed root yields a maximally matched Hungarian tree J in G′
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$ and $r$ a vertex exposed for $M$. Then there is a Hungarian configuration for $(G, M)$ with root $r$: a partition $\mathcal P$ of the vertices into blossom sets for $M$, and in $G' = G/\mathcal P$ an alternating tree $J$ that is planted for $M' = M/\mathcal P$ with root the vertex containing $r$, Hungarian in $G'$, and has every pseudovertex of $G'$ among its outer vertices.
--
--   This is the outcome of "applying the algorithm to $(G, M)$, where $|M|$ is maximum, using some exposed vertex as root" (5.8). By 4.16, "Theorems (4.7) and (4.13) show how by branching a planted tree out from an exposed vertex of $(G, M)$ and shrinking blossoms $B_i$ when they are encountered, we eventually obtain in a graph $G_k = G/B_1/\dots/B_k$ either a tree with an augmenting path or a Hungarian tree"; since $M$ is maximum, no augmenting path arises.
--
--   **Formalization Note** The statement asserts the existence of the configuration the algorithm produces, not the algorithm as a procedure.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 463, 5.8, first sentence (with 4.16, p. 459)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink
import Definitions.Def_PathsTreesFlowers_Duality_HungarianConfig

namespace PathsTreesFlowers.Duality

theorem exists_hungarian_tree_5_8 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMaxMatching G M) (r : V) (hr : IsExposed G M r) :
    ∃ C : HungarianConfig G M, C.root = r := by sorry

end PathsTreesFlowers.Duality
