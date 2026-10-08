-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_2
-- name    : PathsTreesFlowers.Duality.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:25:25.924289+00:00
-- url     : https://prove2.me/theorems/06106299-7fd0-40ca-be47-e8a6979f205c
-- title:
--   4.1–4.2, p. 454 — an alternating tree has one more outer than inner vertex; its maximum matchings leave exactly one outer vertex exposed
-- statement:
--   Let $J$ be an alternating tree in a finite graph $G$, with inner vertices $I$ and outer vertices $O$.
--
--   1. (4.1) $J$ contains one more outer vertex than inner vertices: $|O| = |I| + 1$.
--   2. (4.2) For each outer vertex $v$ of $J$ there is a unique maximum matching of $J$ which leaves $v$ exposed and $v$ the only exposed vertex in $J$.
--   3. (4.2) Every maximum matching of $J$ is one of these: it leaves exactly one vertex of $J$ exposed, and that vertex is outer.
--
--   In particular the maximum cardinality of a matching of an alternating tree equals the number of its inner vertices; this count is used in 4.17.
--
--   **Formalization Note** A matching of $J$ is a matching of $G$ using only edges of $J$; "exposed in $J$" refers to the vertices of $J$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 454, 4.1 (second sentence) and 4.2

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace PathsTreesFlowers.Duality

theorem lemma_4_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) :
    J.outer.card = J.inner.card + 1 ∧
    (∀ v ∈ J.outer, ∃! MJ : Finset E, IsMaxMatchingOn G J.edges MJ ∧
        ∀ w ∈ J.verts, (IsExposed G MJ w ↔ w = v)) ∧
    (∀ MJ : Finset E, IsMaxMatchingOn G J.edges MJ →
        ∃ v ∈ J.outer, ∀ w ∈ J.verts, (IsExposed G MJ w ↔ w = v)) := by sorry

end PathsTreesFlowers.Duality
