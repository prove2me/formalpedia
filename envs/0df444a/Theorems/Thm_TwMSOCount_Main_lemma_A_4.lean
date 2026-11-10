-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_A_4
-- name    : TwMSOCount.Main.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:39.643827+00:00
-- url     : https://prove2.me/theorems/84e8f308-2fe7-410c-a3ad-2f831938ce42
-- title:
--   Lemma A.4 — uniqueness of the farthest minimum separator
-- statement:
--   Let $T_1, T_2$ be disjoint vertex sets of a finite graph $G$. A terminal-disjoint $T_1$–$T_2$ separator is a set $Y\subseteq V(G)\setminus(T_1\cup T_2)$ meeting every path with one endpoint in each terminal set; its reachable side is $L_Y = \{v\notin Y : \text{a path in } G-Y \text{ joins } T_1 \text{ to } v\}$. A farthest minimum separator is a minimum-cardinality separator $Y$ with $L_Z\subseteq L_Y$ for every minimum separator $Z$.
--
--   **Lemma.** If a $T_1$–$T_2$ separator disjoint from $T_1\cup T_2$ exists, then there is exactly one farthest minimum separator from $T_1$.
--
--   The proof is the uncrossing argument behind important separators; it lets the canonical separator be selected by reachability, without an order on vertices.
--
--   Differences from the source:
--   - encoding: paths (length zero allowed) → walks (`SimpleGraph.Walk`, length zero allowed); reason: a set meets every path between two vertices iff it meets every walk between them; reachable sides coincide
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma A.4, p. 16 (PDF 17); Definition A.3

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

namespace TwMSOCount.Main

theorem lemma_A_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (T₁ T₂ : Finset V) (hT : Disjoint T₁ T₂) (hex : ∃ Y, IsTermSep G T₁ T₂ Y) :
    ∃! Y, IsFarthestMinSep G T₁ T₂ Y := by sorry

end TwMSOCount.Main
