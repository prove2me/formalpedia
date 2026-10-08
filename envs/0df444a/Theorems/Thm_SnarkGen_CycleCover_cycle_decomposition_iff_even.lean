-- Prove2me | Theorems.Thm_SnarkGen_CycleCover_cycle_decomposition_iff_even
-- name    : SnarkGen.CycleCover.cycle_decomposition_iff_even
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:42.417997+00:00
-- url     : https://prove2.me/theorems/8036370c-f471-4be5-aa61-f3948072ae77
-- title:
--   §5, p. 15 — a graph decomposes into edge-disjoint cycles iff it is even
-- statement:
--   Let $G$ be a finite simple graph and $S$ a set of edges. Then $S$ is an even subgraph of $G$ ($S \subseteq E(G)$ and every vertex of $G$ lies on an even number of edges of $S$) if and only if $S$ is the disjoint union of the edge sets of cycles of $G$: there is a finite family $\mathcal C$ of pairwise edge-disjoint cycles of $G$ with
--
--   $$S = \bigcup_{C \in \mathcal C} C .$$
--
--   This is Veblen's theorem. The paper uses it to see each colour class of a $k$-CDC as an even subgraph, and it is what turns an even colour class back into cycles when a cycle cover is built in Lemma 7.2. The empty set corresponds to the empty family.
--
--   **Formalization Note** Cycles are edge sets in the sense of `IsCycleEdges`; "pairwise edge-disjoint" is `Set.PairwiseDisjoint` on the family, and the union is `Finset.sup`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 15, Section 5 (unnumbered: "Since a graph has a cycle decomposition into edge-disjoint cycles if and only if it is even")

import Mathlib
import Definitions.Def_SnarkGen_CycleCover_IsCycleEdges
import Definitions.Def_SnarkGen_CycleCover_IsEvenEdgeSet

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, §5, p. 15: a graph has a decomposition into edge-disjoint cycles if and
only if it is even. Stated for a subgraph of `G` given by an edge set `S`. -/
theorem cycle_decomposition_iff_even {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset (Sym2 V)) :
    IsEvenEdgeSet G S ↔
      ∃ 𝒞 : Finset (Finset (Sym2 V)), (∀ C ∈ 𝒞, IsCycleEdges G C) ∧
        (↑𝒞 : Set (Finset (Sym2 V))).PairwiseDisjoint id ∧ 𝒞.sup id = S := by sorry

end SnarkGen.CycleCover
