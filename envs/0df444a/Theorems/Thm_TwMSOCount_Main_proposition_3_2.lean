-- Prove2me | Theorems.Thm_TwMSOCount_Main_proposition_3_2
-- name    : TwMSOCount.Main.proposition_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:06.830808+00:00
-- url     : https://prove2.me/theorems/294a796c-4d3c-4263-b75a-98c109aa6931
-- title:
--   Proposition 3.2 — the canonical separator is well defined and its description satisfies the bounds (2)
-- statement:
--   Let $(H,\chi,\iota)$ be a well-formed colored $B$-boundaried graph with $|B|\le 6(k+1)$, $\mathrm{tw}(H)\le k$ and $m=|H^\circ|>0$, and let $S_\star = S_\star(H,B) = \iota(B_{S,\star})\cup Y_\star\cup\{x_\star\}$ be its canonical separator.
--
--   **Proposition.** $S_\star$ is well defined (exactly one set satisfies its definition). Its canonical description exists — the first $j = |S_\star\setminus\partial H|$ unused labels $N = \{s_1<\dots<s_j\}$ with the increasing label assignment $\eta$ — and has $\eta(s_1)=x_\star$ and separator labels $J = B_{S,\star}\,\dot\cup\, N$ with $j=|N|$; its pieces, with inherited labels $I_i = \iota^{-1}(D_i)$, label sets $B_i = J\,\dot\cup\, I_i$ and internal sizes $m_i = |D_i\setminus\partial H|$, satisfy
--   $$\mathrm{tw}(H_i)\le k,\quad |S_\star|\le k+2,\quad |I_i|\le\lfloor 2|B|/3\rfloor,\quad |B_i|\le 6(k+1),\quad \sum_i m_i = m-j<m. \tag{2}$$
--
--   Applied recursively to the pieces, this gives each graph its unique canonical recursive description.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - encoding: S⋆ is well defined → ∃! S, IsCanonSep H S; reason: uniqueness of the set satisfying the definition
--   - encoding: its canonical description (naming convention) → existence of (N, η) with IsConvLabelAssignment, and the properties for every such (N, η); reason: the convention determines N and η; stating them for all conventional choices is the same
--   - encoding: Σ_i m_i = m − j < m → Σ m_i + |N| = m and Σ m_i < m; reason: avoids truncated subtraction
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Proposition 3.2, p. 7 (PDF 8)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

open Classical

namespace TwMSOCount.Main

theorem proposition_3_2 {r k : ℕ} (H : BGraph r k) (hH : H.WF) (hB : H.B.card ≤ 6 * (k + 1))
    (htw : H.tw ≤ k) (hm : 0 < H.int.card) :
    (∃! S, IsCanonSep H S) ∧
    ∀ S, IsCanonSep H S → ∀ P, IsFirstFeasible H H.B P →
      (∃ (N : Finset (Lab k)) (η : N → H.V), IsConvLabelAssignment H S N η) ∧
      ∀ (N : Finset (Lab k)) (η : N → H.V), IsConvLabelAssignment H S N η →
        (∀ s : N, (∀ t : N, s.1 ≤ t.1) → IsXStar H (η s)) ∧
        labelsIn (extend H N η) S = P.1 ∪ N ∧ Disjoint P.1 N ∧
        N.card = (S \ H.bdry).card ∧
        S.card ≤ k + 2 ∧
        (∀ D ∈ BGraph.comps H.G S,
          (piece (extend H N η) S D).tw ≤ k ∧
          (H.B.filter (fun b => ∃ h : b ∈ H.B, H.ι ⟨b, h⟩ ∈ D)).card ≤ 2 * H.B.card / 3 ∧
          (piece (extend H N η) S D).B =
            (P.1 ∪ N) ∪ H.B.filter (fun b => ∃ h : b ∈ H.B, H.ι ⟨b, h⟩ ∈ D) ∧
          Disjoint (P.1 ∪ N) (H.B.filter (fun b => ∃ h : b ∈ H.B, H.ι ⟨b, h⟩ ∈ D)) ∧
          (piece (extend H N η) S D).B.card ≤ 6 * (k + 1)) ∧
        (∑ D ∈ BGraph.comps H.G S, (D \ H.bdry).card) + N.card = H.int.card ∧
        (∑ D ∈ BGraph.comps H.G S, (D \ H.bdry).card) < H.int.card := by sorry

end TwMSOCount.Main
