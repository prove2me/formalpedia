-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_C_4
-- name    : TwMSOCount.Main.lemma_C_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:48:46.448593+00:00
-- url     : https://prove2.me/theorems/628c5f4a-2ec8-43b5-b532-b0be87962ea9
-- title:
--   Lemma C.4 — the operations of Table 2 are well defined on rank-$q$ types
-- statement:
--   Let $q\ge1$ be the rank of the types (Definition C.2: $q$ is chosen to cover the boundary color tests (rank $0$) and adjacency tests (rank $1$)). Consider colored boundaried graphs with injective boundary maps.
--
--   **Lemma.** The operations of Table 2 induce well-defined partial operations on types: if $H, H'$ (and $H_2, H_2'$) have the same label sets and the same rank-$q$ types, then for introduce, forget and relabel (with their finite data) the results have the same types; AddEdge $(a,b)$ is defined on $H$ iff on $H'$, and then the results have the same type; gluing is defined on $(H_1,H_2)$ iff on $(H_1',H_2')$, and then the results have the same type. Thus input types and finite operation data determine whether the operation is defined and, if so, the output type.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - generalization: the rank chosen in C.4 to cover ψ and all expanded tests → any rank q with 1 ≤ q; reason: boundary adjacency has rank 1; partial-operation definedness and rank-preserving composition need no other test; the rank chosen in the paper satisfies this condition
--   - encoding: AddEdge (a, b) → addEdges {s(a, b)} with AddEdgeOK; reason: same operation
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma C.4, p. 28 (PDF 29); Table 2, p. 27 (PDF 28)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables
import Definitions.Def_TwMSOCount_Main_Types

namespace TwMSOCount.Main

theorem lemma_C_4 {r k : ℕ} (q : ℕ) (hq : 1 ≤ q) :
    (∀ (H H' : BGraph r k) (b : Lab k) (c : Fin r), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B →
      tp q H = tp q H' → b ∉ H.B → tp q (H.introduce b c) = tp q (H'.introduce b c)) ∧
    (∀ (H H' : BGraph r k) (b : Lab k), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B →
      tp q H = tp q H' → b ∈ H.B → tp q (H.forget b) = tp q (H'.forget b)) ∧
    (∀ (H H' : BGraph r k) (π : Lab k → Lab k), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B →
      tp q H = tp q H' → Set.InjOn π ↑H.B → tp q (H.relabel π) = tp q (H'.relabel π)) ∧
    (∀ (H H' : BGraph r k) (a b : Lab k), H.BoundaryWF → H'.BoundaryWF → H.B = H'.B → tp q H = tp q H' →
      (H.AddEdgeOK a b ↔ H'.AddEdgeOK a b) ∧
      (H.AddEdgeOK a b → tp q (H.addEdges {s(a, b)}) = tp q (H'.addEdges {s(a, b)}))) ∧
    (∀ (H₁ H₂ H₁' H₂' : BGraph r k), H₁.BoundaryWF → H₂.BoundaryWF → H₁'.BoundaryWF → H₂'.BoundaryWF →
      H₁.B = H₁'.B → H₂.B = H₂'.B → tp q H₁ = tp q H₁' → tp q H₂ = tp q H₂' →
      (BGraph.GlueOK H₁ H₂ ↔ BGraph.GlueOK H₁' H₂') ∧
      (BGraph.GlueOK H₁ H₂ → tp q (BGraph.glue H₁ H₂) = tp q (BGraph.glue H₁' H₂'))) := by sorry

end TwMSOCount.Main
