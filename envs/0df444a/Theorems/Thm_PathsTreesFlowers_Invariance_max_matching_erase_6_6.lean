-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_max_matching_erase_6_6
-- name    : PathsTreesFlowers.Invariance.max_matching_erase_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:47.503494+00:00
-- url     : https://prove2.me/theorems/5659ccc1-3331-478e-8bcc-06da7032c945
-- title:
--   6.6, p. 465 — a non-outer vertex v meets an edge e of M, and M − e is a maximum matching of G − v
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^*$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ as in 6.2. Let $v$ be a vertex of $G$ with $v \notin O(G)$. Then:
--
--   1. $v$ meets an edge $e$ of $M$;
--   2. for every edge $e \in M$ meeting $v$,
--   $$M - e \text{ is a maximum matching of } G - v,$$
--   where $G - v$ is the graph obtained from $G$ by deleting $v$ and its adjoining edges.
--
--   This is the key step of Witzgall's proof of the converse half of 6.2 (a).
--
--   **Formalization Note** $G - v$ is the subgraph induced on the vertices other than $v$; a maximum matching of it is a matching of $G$ avoiding $v$ of largest cardinality among such matchings. The configuration is the structure `Config60`.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 465, 6.6 (first two paragraphs)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.6, p. 465: a non-outer vertex `v` meets an edge `e` of `M`, and for such an edge `M − e` is
a maximum matching of `G − v` (the subgraph induced on the vertices other than `v`). -/
theorem max_matching_erase_6_6 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) (v : V) (hv : v ∉ outerSet C) :
    (∃ e ∈ M, v ∈ G.ends e) ∧
    ∀ e ∈ M, v ∈ G.ends e → IsMaxMatchingIn G (induced G (Finset.univ.erase v)) (M.erase e) := by sorry

end PathsTreesFlowers.Invariance
