-- Prove2me | Theorems.Thm_VDCyclePack_lemma_6_1
-- name    : VDCyclePack.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:39.574199+00:00
-- url     : https://prove2.me/theorems/a1407a00-9148-438c-8b11-89fe39ef8a5d
-- title:
--   Lemma 6.1: the $d$ subpaths of $C$ between consecutive contacts are $A$-paths, every vertex on at most two of them
-- statement:
--   Let $H$ be a marked packing of a finite graph $G$, $A=V(H)$, and let $C$ be a cycle with $d=c_H(C)\ge2$ contacts. Then the $d$ subpaths $R_1,\dots,R_d$ of $C$ between consecutive contacts are $A$-paths of $G-E(H)$, and every vertex of $C$ lies on at most two of them.
--
--   Each of these subpaths must meet a set meeting all $A$-paths, which gives the contact bound of Lemma 6.4.
--
--   **Formalization Note** The subpaths between consecutive contacts are described as $d$ walks of $G$ that use only edges of $C$, no edge of $H$, pairwise share no edge and together cover $E(C)\setminus E(H)$; for $d\ge2$ these are exactly the subpaths between consecutive contacts.
--
--   Differences from the source:
--   - encoding: a marked packing H, A = V(H), A-paths in G − E(H) → H = P.sup id for a cycle packing P (a Finset of pairwise vertex-disjoint cycle subgraphs); A = H.verts; A-paths are IsAPath in G.deleteEdges H.edgeSet; reason: the paper's definitions (pp.10–11); same instances
--   - encoding: c_H(C), C(H, L, c), n = |V(G)| → contacts (components of the subgraph meet C ⊓ H), candidates G H L c, Fintype.card V; reason: the paper's definitions (pp.10, 13); same instances
--   - encoding: the d subpaths of C between consecutive contacts → d = contacts walks p i of G, each IsAPath for A = V(H) with no edge in E(H), all edges in E(C), pairwise edge-disjoint, covering E(C) \ E(H); reason: an A-path inside C avoiding E(H) runs between consecutive contacts, and d edge-disjoint ones are all d subpaths; same statement
--   - encoding: every vertex of C lies on at most two of them → every vertex w of G lies on the supports of at most two p i; reason: the walks lie in C, so vertices outside C lie on none
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 6.1, p.18

import Mathlib
import Definitions.Def_VDCyclePack_IsCyclePacking
import Definitions.Def_VDCyclePack_cycles
import Definitions.Def_VDCyclePack_contacts
import Definitions.Def_VDCyclePack_IsAPath

namespace VDCyclePack

open Classical in
/-- **Lemma 6.1 (contacts give A-paths).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 6.1, p.18: "Let C be a cycle with d = c_H(C) ≥ 2 contacts. The d subpaths of C
between consecutive contacts are A-paths, and every vertex of C lies on at most two of them." Here
`H` is a marked packing, `A = V(H)`, and A-paths lie in `G − E(H)` (p.11, p.18).

Let `P` be a cycle packing of `G`, `H = ⋃ P`, `A = V(H)`, and let `C` be a cycle of `G` with
`d = c_H(C) ≥ 2` contacts. Then there are `d` walks `p₁, …, p_d` of `G` such that: each `pᵢ` is an
A-path using no edge of `H`; each `pᵢ` uses only edges of `C`; distinct `pᵢ` share no edge; every
edge of `C` not in `H` is an edge of some `pᵢ`; and every vertex lies on at most two of the `pᵢ`.

**Formalization Note.** "The d subpaths of C between consecutive contacts" are pinned down as the
`d` edge-disjoint A-paths inside `C` that avoid `E(H)` and cover `E(C) ∖ E(H)`: these are exactly the
maximal stretches of `C` outside the contacts. An A-path with no edge of `H` is an A-path of
`G − E(H)`. -/
theorem lemma_6_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hP : IsCyclePacking P) (C : G.Subgraph) (hC : C ∈ cycles G)
    (hd : 2 ≤ contacts (P.sup id) C) :
    ∃ (u v : Fin (contacts (P.sup id) C) → V) (p : ∀ i, G.Walk (u i) (v i)),
      (∀ i, IsAPath G (P.sup id).verts (p i) ∧ ∀ e ∈ (p i).edges, e ∉ (P.sup id).edgeSet) ∧
      (∀ i, ∀ e ∈ (p i).edges, e ∈ C.edgeSet) ∧
      (∀ i j, i ≠ j → List.Disjoint (p i).edges (p j).edges) ∧
      (∀ e ∈ C.edgeSet, e ∉ (P.sup id).edgeSet → ∃ i, e ∈ (p i).edges) ∧
      ∀ w : V, (Finset.univ.filter fun i => w ∈ (p i).support).card ≤ 2 := by sorry

end VDCyclePack
