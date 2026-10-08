-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_lemma_5_7
-- name    : PathsTreesFlowers.Duality.lemma_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:32:08.221998+00:00
-- url     : https://prove2.me/theorems/7cf67f04-0cdb-48e3-a444-3b3ee7c77d9c
-- title:
--   5.7, p. 463 — the theorem holds for a graph with a matching leaving at most one exposed vertex
-- statement:
--   Let $M$ be a matching of a finite graph $G$ with at most one exposed vertex (a perfect matching, or a matching with one exposed vertex). Then there is an odd-set cover $\mathcal S$ of $G$ with
--
--   $$\operatorname{cap}(\mathcal S) = |M|.$$
--
--   Together with weak duality this proves the matching-duality theorem for such graphs; it is the base case of Edmonds' induction on the number of exposed vertices.
--
--   **Formalization Note** The paper names specific covers: for a perfect matching, one singleton and the set of all other vertices; for one exposed vertex, the set of all vertices. These fail in degenerate cases (two vertices joined by an edge: two singletons, capacity $2 \ne 1$; one vertex and no edge: one singleton, capacity $1 \ne 0$), while the claim that the theorem holds remains true there. The statement therefore asserts the existence of a cover, not the page's specific families.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 463, 5.7

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover

namespace PathsTreesFlowers.Duality

theorem lemma_5_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (hexp : (Finset.univ.filter (IsExposed G M)).card ≤ 1) :
    ∃ S : Finset (Finset V), IsOddSetCover G S ∧ capacitySum S = M.card := by sorry

end PathsTreesFlowers.Duality
