-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_A_5
-- name    : TwMSOCount.Main.lemma_A_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:22.570859+00:00
-- url     : https://prove2.me/theorems/cdd5d859-acbc-462c-bfa1-299ed2ae29e0
-- title:
--   Lemma A.5 — boundary bounds and recursive progress for a feasible partition plus one internal vertex
-- statement:
--   Let $(H,\chi,\iota)$ be a well-formed colored $B$-boundaried graph with $b = |B|\le 6(k+1)$, $\mathrm{tw}(H)\le k$ and $m = |H^\circ|>0$. Let $P = (B_S,B_L,B_R)$ be eligible and feasible, $Y_P$ its farthest minimum internal separator, $t\in H^\circ$, $S = \iota(B_S)\cup Y_P\cup\{t\}$ and $j = |S\setminus\partial H|$. For the components $D_i$ of $H-S$ put $I_i=\iota^{-1}(D_i)$ and $m_i = |D_i\setminus\partial H|$.
--
--   **Lemma.** $S\cap\partial H = \iota(B_S)$, $1\le j$, $|S|\le k+2$, and
--   $$|I_i|\le\lfloor 2b/3\rfloor,\qquad \sum_{i=1}^p m_i = m-j < m .$$
--   There are at least $j$ unused labels in $\Lambda_k\setminus B$, and for any such label set $N$ and bijection $\eta:N\to S\setminus\partial H$ the piece label sets $B_i = B_S\cup N\cup I_i$ satisfy $|B_i|\le 6(k+1)$.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - encoding: Σ m_i = m − j < m → Σ m_i + j = m and Σ m_i < m; reason: avoids truncated subtraction
--   - encoding: Y_P (unique by Lemma A.4) → any Y with IsYP H B P Y; reason: Y_P is defined as the set with this property
--   - encoding: at least j unused labels in Λ_k \ B → j ≤ |Λ_k \ B|; reason: same statement
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma A.5, p. 17 (PDF 18)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

open Classical

namespace TwMSOCount.Main

theorem lemma_A_5 {r k : ℕ} (H : BGraph r k) (hH : H.WF) (hB : H.B.card ≤ 6 * (k + 1))
    (htw : H.tw ≤ k) (hm : 0 < H.int.card) (P : BPart k) (hel : Eligible H.B P)
    (hfe : Feasible H H.B P) (Y : Finset H.V) (hY : IsYP H H.B P Y) (t : H.V) (ht : t ∈ H.int) :
    (H.img P.1 ∪ Y ∪ {t}) ∩ H.bdry = H.img P.1 ∧
    1 ≤ ((H.img P.1 ∪ Y ∪ {t}) \ H.bdry).card ∧
    (H.img P.1 ∪ Y ∪ {t}).card ≤ k + 2 ∧
    (∀ D ∈ BGraph.comps H.G (H.img P.1 ∪ Y ∪ {t}),
      (H.B.filter (fun b => ∃ h : b ∈ H.B, H.ι ⟨b, h⟩ ∈ D)).card ≤ 2 * H.B.card / 3) ∧
    (∑ D ∈ BGraph.comps H.G (H.img P.1 ∪ Y ∪ {t}), (D \ H.bdry).card) +
        ((H.img P.1 ∪ Y ∪ {t}) \ H.bdry).card = H.int.card ∧
    (∑ D ∈ BGraph.comps H.G (H.img P.1 ∪ Y ∪ {t}), (D \ H.bdry).card) < H.int.card ∧
    ((H.img P.1 ∪ Y ∪ {t}) \ H.bdry).card ≤ (Finset.univ \ H.B).card ∧
    ∀ (N : Finset (Lab k)), N ⊆ Finset.univ \ H.B →
      N.card = ((H.img P.1 ∪ Y ∪ {t}) \ H.bdry).card →
      ∀ η : N → H.V, IsLabelAssignment H (H.img P.1 ∪ Y ∪ {t}) N η →
      ∀ D ∈ BGraph.comps H.G (H.img P.1 ∪ Y ∪ {t}),
        (P.1 ∪ N ∪ H.B.filter (fun b => ∃ h : b ∈ H.B, H.ι ⟨b, h⟩ ∈ D)).card ≤ 6 * (k + 1) := by sorry

end TwMSOCount.Main
