-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_cover_step_5_8
-- name    : PathsTreesFlowers.Duality.cover_step_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:48:52.975696+00:00
-- url     : https://prove2.me/theorems/092472dd-0c7f-4de7-954d-f8d03d329626
-- title:
--   5.8, p. 463 — S_J covers exactly the edges outside G′ − J, each M-edge there once, and M ∩ (G′ − J) is maximum with one less exposed vertex
-- statement:
--   Let $M$ be a maximum matching of a finite graph $G$ and take a Hungarian configuration for $(G, M)$: $G' = G/\mathcal P$, the tree $J$, the vertex set $X$ of $G' - J$ and the family $\mathcal S_J$ of odd sets (one inner vertex of $J$; the complete expansion of one pseudovertex of $J$). Then
--
--   1. every member of $\mathcal S_J$ is an odd set;
--   2. the number of edges of $M$ which a member of $\mathcal S_J$ covers equals the capacity of the member;
--   3. every edge of $M$ not in $G' - J$ is covered by exactly one member of $\mathcal S_J$;
--   4. an edge of $G$ is covered by a member of $\mathcal S_J$ if and only if it is not in $G' - J$;
--   5. $M \cap (G' - J)$ is a maximum matching of $G' - J$,
--   6. with one less exposed vertex than $(G, M)$;
--   7. consequently
--   $$|M| = \operatorname{cap}(\mathcal S_J) + |M \cap (G' - J)|.$$
--
--   This is the induction step of Edmonds' proof of the matching-duality theorem: if $|M \cap (G'-J)|$ equals the capacity-sum of an odd-set cover $\mathcal S'_J$ of $G' - J$, then $|M|$ equals the capacity-sum of the odd-set cover $\mathcal S_J \cup \mathcal S'_J$ of $G$.
--
--   **Formalization Note** $G' - J$ is expressed in terms of $G$: its edges are the edges of $G$ with both end-points in $X$, its exposed vertices are the vertices of $X$ meeting no edge of $M$ with both end-points in $X$. Item 7 is the identity the paper derives from 2 and 3.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 463, 5.8

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover
import Definitions.Def_PathsTreesFlowers_Duality_HungarianConfig

namespace PathsTreesFlowers.Duality

theorem cover_step_5_8 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMaxMatching G M) (C : HungarianConfig G M) :
    (∀ U ∈ C.SJ, IsOddSet U) ∧
    (∀ U ∈ C.SJ, (M.filter (Covers G U)).card = capacity U) ∧
    (∀ e ∈ M, G.ends e ∉ C.X.sym2 → (C.SJ.filter (fun U => Covers G U e)).card = 1) ∧
    (∀ e : E, (∃ U ∈ C.SJ, Covers G U e) ↔ G.ends e ∉ C.X.sym2) ∧
    IsMaxMatchingIn G (induced G C.X) (M ∩ edgesWithin G C.X) ∧
    (exposedIn G C.X M).card + 1 = (Finset.univ.filter (IsExposed G M)).card ∧
    M.card = capacitySum C.SJ + (M ∩ edgesWithin G C.X).card := by sorry

end PathsTreesFlowers.Duality
