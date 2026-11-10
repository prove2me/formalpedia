-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_C_6
-- name    : TwMSOCount.Main.lemma_C_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:48:22.22155+00:00
-- url     : https://prove2.me/theorems/5d85c380-1f6c-427c-9bf6-baca76189554
-- title:
--   Lemma C.6 — every bounded-boundary graph of treewidth at most $k$ is the value of a construction term
-- statement:
--   Construction terms (Definition C.5) are built from the empty graph by the operations of Table 2 (introduce, forget, relabel, AddEdge, glue) with labels in $\Lambda_k$; the value of a term is specified up to isomorphism preserving colors and boundary labels.
--
--   **Lemma.** Every colored $B$-boundaried graph with injective boundary map with $|B|\le 6(k+1)$ and treewidth at most $k$ is the value of a construction term. The same holds for graphs on at most $6(k+1)$ boundary vertices alone, without a width restriction.
--
--   This coverage is what makes the saturation of Section 5 reach the state of every graph the recurrences use.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - encoding: is the value of a construction term (up to isomorphism preserving colors and boundary labels) → ∃ t H', t.value = some H' ∧ IsoBL H' H; reason: Definition C.5 specifies values up to this isomorphism
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma C.6, p. 30 (PDF 31)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables
import Definitions.Def_TwMSOCount_Main_Types

namespace TwMSOCount.Main

theorem lemma_C_6 {r k : ℕ} :
    (∀ H : BGraph r k, H.BoundaryWF → H.B.card ≤ 6 * (k + 1) → H.tw ≤ k →
      ∃ (t : CTerm r k) (H' : BGraph r k), t.value = some H' ∧ BGraph.IsoBL H' H) ∧
    (∀ H : BGraph r k, H.BoundaryWF → H.B.card ≤ 6 * (k + 1) → H.int = ∅ →
      ∃ (t : CTerm r k) (H' : BGraph r k), t.value = some H' ∧ BGraph.IsoBL H' H) := by sorry

end TwMSOCount.Main
