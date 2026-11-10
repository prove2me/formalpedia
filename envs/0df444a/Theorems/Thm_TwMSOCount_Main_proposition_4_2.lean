-- Prove2me | Theorems.Thm_TwMSOCount_Main_proposition_4_2
-- name    : TwMSOCount.Main.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:46:31.643207+00:00
-- url     : https://prove2.me/theorems/fa406900-da92-4cf9-a5d1-de0446ed6788
-- title:
--   Proposition 4.2 — the evaluation order is well founded: every right-hand-side entry is computed earlier
-- statement:
--   Fix a state map for $\theta$ and consider the graph entries $G_B(m,\tau)$ and collection entries $U_\gamma(I,m,\tau)$ of Section 4.2 with their recurrences (3)–(8). Rank the entries by
--   $$\mathrm{rank}(G_B(m,\tau)) = (m,0,0),\qquad \mathrm{rank}(U_\gamma(I,m,\tau)) = (m,1,|I|),$$
--   compared lexicographically; this is the order "for $m=0,1,\dots,n$, first all graph entries at size $m$, then all collection entries at size $m$ in increasing order of $|I|$".
--
--   **Proposition.** Every entry used on the right-hand side of the recurrence of an existing entry is an existing entry of strictly smaller rank, so it has already been computed.
--
--   Here a graph entry is used by a collection recurrence through the filtered piece query (4), which reads it only when the filter passes.
--
--   Differences from the source:
--   - encoding: a state map (Definition 4.1); the test Φ_{B,B_S,N} → StateMap with IsStateMap ψ (states coded by ℕ, finite sets T_B); Φ_{B,B_S,N} by its meaning PhiT from Appendix C.2; reason: Appendix C.2 gives the truth of Φ on every structure as First_{B,P} ∧ Sel_{B,P,N}; the computability of the bounds on |T_B| is meaningful only uniformly in θ and is the content of Proposition 5.1
--   - encoding: computed earlier in the order of Proposition 4.2 → Entry.Valid of the used entry and RankLt of its rank (12); reason: the evaluation order is the lexicographic order of ranks over the existing entries
--   - reading: entries used on the right-hand side → `Uses`: the collection entry of a parent summand; the graph entry of a piece summand when the filter (4) passes, and the remaining collection entry; reason: the filtered query (4) is a query to G only when its condition holds; otherwise its value is 0 and nothing is read
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Proposition 4.2, p. 11 (PDF 12); proof in Appendix B.3, p. 19 (PDF 20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables

namespace TwMSOCount.Main

theorem proposition_4_2 {r k : ℕ} [NeZero r] (ψ : Formula r Empty) (hψ : ψ.IsSentence)
    (SM : StateMap r k) (hSM : SM.IsStateMap ψ) (e e' : Entry r k) (he : e.Valid SM)
    (huse : Uses SM e e') :
    e'.Valid SM ∧ RankLt e'.rank e.rank := by sorry

end TwMSOCount.Main
