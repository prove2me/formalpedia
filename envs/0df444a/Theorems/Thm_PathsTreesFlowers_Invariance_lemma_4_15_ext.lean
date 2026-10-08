-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_15_ext
-- name    : PathsTreesFlowers.Invariance.lemma_4_15_ext
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:11.080004+00:00
-- url     : https://prove2.me/theorems/244ddba6-9ce1-4d76-b326-0619760feca4
-- title:
--   4.15, extension, forest form (4.20), pp. 459–460 — if M/P is maximum and the shrunken sets are outer in a planted forest, M is maximum
-- statement:
--   Let $G$ be a finite graph, $M$ a matching of $G$, and $\mathcal P$ a partition of the vertices of $G$ whose parts with more than one vertex are the disjoint subgraphs $P_1, \dots, P_n$ to be shrunk; write $G_n = G/\mathcal P$ and $M_n = M/\mathcal P = M \cap G_n$. Assume each part induces a connected subgraph, and:
--
--   1. $M \cap P_i^+$ leaves exactly one exposed vertex in $P_i$, for each $i$;
--   2. $M_n$ is a maximum matching of $G_n$;
--   3. the vertices $P_i/P_i$ of $G_n$ are outer vertices in a planted forest for $(G_n, M_n)$: a family of disjoint planted trees $J_1, \dots, J_m$ for $M_n$ in $G_n$, each $P_i/P_i$ an outer vertex of some $J_j$.
--
--   Then
--   $$M \text{ is a maximum matching of } G.$$
--
--   The paper states this for a single planted tree $J_n$ and remarks (4.20) that "the theorems on trees presented in this section are essentially the same for forests"; the forest form is the one needed when the trees of Section 6 are grown from all exposed vertices.
--
--   **Formalization Note** The paper's family $P_1, \dots, P_n$ of disjoint subgraphs is encoded by the non-singleton parts of a partition; a singleton $P_i$ would satisfy (1) trivially, so nothing is lost. Shrinking is defined in 4.9 only for connected $H$, so connectedness of each $P_i^+$ is stated as a hypothesis (it is a standing assumption of the paper's shrinking operation, not an addition to the theorem).
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 459, 4.15 ('The theorem extends as follows'); p. 460, 4.20 (planted forest; 'The theorems on trees presented in this section are essentially the same for forests'); p. 457, 4.9 (shrinking connected H)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace PathsTreesFlowers.Invariance

open EdmondsMatching65.Polyhedron (IsMatching)

/-- 4.15, extension (p. 459), in the forest form of 4.20 (p. 460). Let `M` be a matching of `G`
and let the parts of `P` with more than one vertex be the disjoint subgraphs `P₁, …, Pₙ`, each
inducing a connected subgraph, such that (1) `M ∩ Pᵢ⁺` leaves exactly one exposed vertex in `Pᵢ`,
(2) `M/P` is a maximum matching of `G/P`, and (3) the vertices `Pᵢ/Pᵢ` are outer vertices of a
planted forest for `(G/P, M/P)`. Then `M` is a maximum matching of `G`. -/
theorem lemma_4_15_ext {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (P : Finpartition (Finset.univ : Finset V))
    (hconn : ∀ U ∈ P.parts, (induced G U).Connected)
    (h1 : ∀ U ∈ P.parts, 1 < U.card →
      ∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) w ↔ w = u))
    (h2 : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M))
    (n : ℕ) (J : Fin n → AltTree (shrink G P))
    (hJ : ∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J i) r)
    (hdisj : ∀ i j, i ≠ j → Disjoint (J i).verts (J j).verts)
    (h3 : ∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card → ∃ i, ⟨U, hU⟩ ∈ (J i).outer) :
    PathsTreesFlowers.Duality.IsMaxMatching G M := by sorry

end PathsTreesFlowers.Invariance
