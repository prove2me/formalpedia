-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_theorem_6_2
-- name    : PathsTreesFlowers.Invariance.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:12.758111+00:00
-- url     : https://prove2.me/theorems/d1759df5-e237-4aed-a13a-91619b719980
-- title:
--   Theorem 6.2 (a)–(c), p. 464 — O(G) is exactly the set of vertices exposed by some maximum matching; I(G) are its neighbours; G* shrinks the components of O(G)⁺
-- statement:
--   Let $G$ be a finite graph and $M$ any maximum matching of $G$. Let $G^* = G/\mathcal P$ and the planted trees $J_1, \dots, J_n$ be obtained from $(G, M)$ by construction 6.0, and let $O(G)$ (the non-pseudo outer vertices of the $J_i$ together with the vertices of the pseudovertex complete expansions) and $I(G)$ (the inner vertices of the $J_i$) be as defined there. Then:
--
--   1. **(a)** the outer vertices $O(G)$ are precisely the vertices of $G$ left exposed by some maximum matching of $G$:
--   $$v \in O(G) \iff \exists M' \text{ maximum matching of } G \text{ with } v \text{ exposed for } M';$$
--   2. **(b)** the inner vertices $I(G)$ are precisely the vertices of $G$ not in $O(G)$ but joined to vertices in $O(G)$;
--   3. **(c)** $G^*$ is obtained from $G$ by shrinking the connected components of $O(G)^+$, the subgraph of $G$ consisting of the vertices $O(G)$ and all edges of $G$ joining them: two vertices $u, v$ lie in the same part of $\mathcal P$ if and only if $u = v$ or $u, v$ lie in the same connected component of $O(G)^+$.
--
--   Thus $O(G)$, $I(G)$ and $G^*$ depend only on $G$, not on the maximum matching or on the order in which the trees were grown. This is the first appearance of what is now called the Gallai–Edmonds structure theorem: the vertices that some maximum matching misses, their neighbours, and the remaining vertices form a canonical decomposition of every graph.
--
--   **Formalization Note** The output of construction 6.0 is the structure `Config60`, which records every invariant of the construction (maximum $M$; parts of $\mathcal P$ are blossom sets for $M$; disjoint planted trees for $M/\mathcal P$; density; $J_i$ Hungarian in $G^* - J_1 - \dots - J_{i-1}$; pseudovertices outer). The theorem is stated for every such configuration; that one exists for every maximum matching is the separate item `exists_config_6_0`.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 464, 6.2 (a), (b), (c)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config

namespace PathsTreesFlowers.Invariance

/-- Theorem 6.2, p. 464. For `(G, M)` with `M` any maximum matching, let `G*` and `{Jᵢ}` be
obtained from `(G, M)` by 6.0 (the data `C`). (a) The outer vertices `O(G)` are precisely the
vertices of `G` left exposed by some maximum matching of `G`. (b) The inner vertices `I(G)` are
precisely the vertices not in `O(G)` but joined to vertices in `O(G)`. (c) `G*` is obtained from
`G` by shrinking the connected components of `O(G)⁺`. -/
theorem theorem_6_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) :
    (∀ v : V, v ∈ outerSet C ↔ ∃ M' : Finset E, PathsTreesFlowers.Duality.IsMaxMatching G M' ∧ PathsTreesFlowers.Duality.IsExposed G M' v) ∧
    (∀ v : V, v ∈ innerSet C ↔
      v ∉ outerSet C ∧ ∃ u ∈ outerSet C, ∃ e : E, G.ends e = s(u, v)) ∧
    (∀ u v : V, C.P.part u = C.P.part v ↔
      (u = v ∨ (u ∈ outerSet C ∧ v ∈ outerSet C ∧
        Relation.ReflTransGen
          (fun x y => x ∈ outerSet C ∧ y ∈ outerSet C ∧ ∃ e : E, G.ends e = s(x, y)) u v))) := by sorry

end PathsTreesFlowers.Invariance
