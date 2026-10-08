-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_matching_duality_theorem
-- name    : PathsTreesFlowers.Duality.matching_duality_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:32:22.444181+00:00
-- url     : https://prove2.me/theorems/7f40fed4-a91a-48ba-80bc-a255b73639ec
-- title:
--   5.6 (Matching-Duality Theorem), p. 462 — the maximum cardinality of a matching equals the minimum capacity-sum of an odd-set cover
-- statement:
--   Let $G$ be a finite graph (every edge meets exactly two distinct vertices; parallel edges allowed). Then there exist a maximum-cardinality matching $M$ of $G$ and a minimum-capacity odd-set cover $\mathcal S$ of $G$ with
--
--   $$|M| = \operatorname{cap}(\mathcal S) = \sum_{U \in \mathcal S} \operatorname{cap}(U).$$
--
--   In words: the maximum cardinality of a matching in $G$ equals the minimum capacity-sum of an odd-set cover in $G$, where a single vertex has capacity $1$ and covers the edges meeting it, and a set of $2k+1$ vertices ($k \ge 1$) has capacity $k$ and covers the edges with both end-points in it.
--
--   This min–max theorem is the integral linear-programming duality behind maximum matching in general graphs. It generalizes König's theorem for bipartite graphs and is equivalent to the Tutte–Berge formula; an optimal cover is a short certificate that a matching is maximum.
--
--   **Formalization Note** Since everything is finite, a maximum matching and a minimum odd-set cover both exist; the content of the statement is the equality of their sizes.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 462, 5.6 (Matching-Duality Theorem)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

namespace PathsTreesFlowers.Duality

theorem matching_duality_theorem {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) :
    ∃ M : Finset E, IsMaxMatching G M ∧
      ∃ S : Finset (Finset V), IsMinOddSetCover G S ∧ M.card = capacitySum S := by sorry

end PathsTreesFlowers.Duality
