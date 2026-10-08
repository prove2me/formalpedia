-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_2
-- name    : PathsTreesFlowers.Invariance.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:17.028759+00:00
-- url     : https://prove2.me/theorems/c45086d0-84ae-472f-a0a5-736fcc1d16fb
-- title:
--   4.1 and 4.2, p. 454 — an alternating tree has one more outer than inner vertex; its maximum matchings each leave exactly one outer vertex exposed
-- statement:
--   Let $J$ be an alternating tree in a finite graph $G$, with inner vertices $I(J)$ and outer vertices $O(J)$. Then:
--
--   1. $J$ contains one more outer vertex than inner vertices:
--   $$|O(J)| = |I(J)| + 1;$$
--   2. for each outer vertex $v$ of $J$ there is a unique maximum matching of $J$ which leaves $v$ exposed and leaves no other vertex of $J$ exposed;
--   3. every maximum matching of $J$ is one of these: it leaves exactly one vertex of $J$ exposed, and that vertex is outer.
--
--   This is the basic structural fact about alternating trees: the maximum matchings of a tree are indexed by its outer vertices, and their cardinality is the number of inner vertices. It underlies planted trees (4.3), the Hungarian-tree argument (4.17) and the proof of 6.2.
--
--   **Formalization Note** A matching of $J$ is a matching of $G$ contained in the edge set of $J$; "exposed in $J$" is exposure for that matching, restricted to vertices of $J$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 454, 4.1 (italic sentence) and 4.2

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace PathsTreesFlowers.Invariance

/-- 4.1 (count) and 4.2, p. 454: an alternating tree has one more outer vertex than inner
vertices; for each outer vertex `v` there is a unique maximum matching of the tree leaving `v`
and only `v` exposed in the tree; every maximum matching of the tree is one of these. -/
theorem lemma_4_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) :
    J.outer.card = J.inner.card + 1 ∧
    (∀ v ∈ J.outer, ∃! N : Finset E,
      IsMaxMatchingIn G J.toSub N ∧ ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G N w ↔ w = v)) ∧
    (∀ N : Finset E, IsMaxMatchingIn G J.toSub N →
      ∃ v ∈ J.outer, ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G N w ↔ w = v)) := by sorry

end PathsTreesFlowers.Invariance
