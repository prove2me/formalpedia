-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_A_2
-- name    : TwMSOCount.Main.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:30.942974+00:00
-- url     : https://prove2.me/theorems/8f480d17-971e-43b3-8ff0-74f460ace4e9
-- title:
--   Lemma A.2 — if $\mathrm{tw}(H)\le k$, an eligible feasible partition of $B$ exists
-- statement:
--   Let $(H,\chi,\iota)$ be a well-formed colored $B$-boundaried graph. A partition $P = (B_S,B_L,B_R)$ of $B$ is **eligible** if $|B_S|\le k+1$ and $|B_L|,|B_R|\le\lfloor 2|B|/3\rfloor$, and **feasible** if some $Y\subseteq H^\circ$ with $|Y|\le (k+1)-|B_S|$ meets every path from $\iota(B_L)$ to $\iota(B_R)$ in $H-\iota(B_S)$.
--
--   **Lemma.** If $\mathrm{tw}(H)\le k$, then an eligible feasible partition of $B$ exists in $H$.
--
--   This is the balanced-separator step that makes the canonical separator well defined (Proposition 3.2); the threshold $\lfloor 2|B|/3\rfloor$ is what keeps piece boundaries bounded by $6(k+1)$.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - encoding: |Y| ≤ (k+1) − |B_S| → Y.card + B_S.card ≤ k + 1; reason: avoids truncated subtraction; equal for eligible P
--   - encoding: meets every path → meets the support of every walk in H with ι(B_S) isolated; reason: a set meets every path between two sets iff it meets every walk between them
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma A.2, p. 16 (PDF 17)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

namespace TwMSOCount.Main

theorem lemma_A_2 {r k : ℕ} (H : BGraph r k) (hH : H.WF) (htw : H.tw ≤ k) :
    ∃ P : BPart k, Eligible H.B P ∧ Feasible H H.B P := by sorry

end TwMSOCount.Main
