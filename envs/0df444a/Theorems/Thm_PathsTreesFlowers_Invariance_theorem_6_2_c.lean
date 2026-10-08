-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_theorem_6_2_c
-- name    : PathsTreesFlowers.Invariance.theorem_6_2_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:33.299901+00:00
-- url     : https://prove2.me/theorems/319e0e9f-9733-42ff-9751-dbc278bfff13
-- title:
--   6.2 (c), p. 464 — G* is obtained from G by shrinking the connected components of O(G)⁺
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$, and let $G^* = G/\mathcal P$ and $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, with outer vertices $O(G)$ as in 6.2. Let $O(G)^+$ be the subgraph of $G$ consisting of the vertices $O(G)$ and all edges of $G$ joining them. Then $G^*$ is obtained from $G$ by shrinking the connected components of $O(G)^+$: for all vertices $u, v$ of $G$,
--   $$u, v \text{ lie in the same part of } \mathcal P \iff u = v \ \text{ or } \ u, v \text{ lie in the same connected component of } O(G)^+.$$
--
--   In particular the vertices outside $O(G)$ are not shrunk, each non-pseudo outer vertex is a one-vertex component of $O(G)^+$, and each pseudovertex of $G^*$ is the vertex set of a component of $O(G)^+$. Hence $G^*$ is determined by $G$ alone.
--
--   **Formalization Note** "Same connected component of $O(G)^+$" is the reflexive–transitive closure of adjacency by an edge of $G$ with both end-points in $O(G)$, required together with $u, v \in O(G)$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 464, 6.2 (c); proof in 6.4, second paragraph

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- 6.2 (c), p. 464: `G*` is obtained from `G` by shrinking the connected components of `O(G)⁺`.
Two vertices lie in the same part of `P` (the same vertex of `G*`) iff they are equal or both
lie in `O(G)` and are joined by a sequence of edges of `G` with all end-points in `O(G)`. -/
theorem theorem_6_2_c {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    ∀ u v : V, C.P.part u = C.P.part v ↔
      (u = v ∨ (u ∈ outerSet C ∧ v ∈ outerSet C ∧
        Relation.ReflTransGen
          (fun x y => x ∈ outerSet C ∧ y ∈ outerSet C ∧ ∃ e : E, G.ends e = s(x, y)) u v)) := by sorry

end PathsTreesFlowers.Invariance
