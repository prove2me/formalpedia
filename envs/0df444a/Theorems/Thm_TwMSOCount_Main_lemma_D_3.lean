-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_D_3
-- name    : TwMSOCount.Main.lemma_D_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:47:21.741292+00:00
-- url     : https://prove2.me/theorems/44e818a7-59dc-4e3b-8084-a31c5e4f84a3
-- title:
--   Lemma D.3 — a complete sample uses $O_k(n)$ graph and collection calls
-- statement:
--   A run of the recursive sampler of Algorithm 2 from the empty boundary with $n$ internal vertices follows one expanded description of a root entry $G_\emptyset(n,\tau)$; each node of the description is one graph call or one collection call.
--
--   **Lemma.** There is a constant $C_k$ depending only on $k$ such that every complete sample from the empty boundary with $n$ internal vertices uses at most $C_k\,(n+1)$ graph and collection calls in total, i.e. $O_k(n)$ calls.
--
--   Differences from the source:
--   - encoding: a state map (Definition 4.1); the test Φ_{B,B_S,N} → StateMap with IsStateMap ψ (states coded by ℕ, finite sets T_B); Φ_{B,B_S,N} by its meaning PhiT from Appendix C.2; reason: Appendix C.2 gives the truth of Φ on every structure as First_{B,P} ∧ Sel_{B,P,N}; the computability of the bounds on |T_B| is meaningful only uniformly in θ and is the content of Proposition 5.1
--   - encoding: a complete sample uses O_k(n) calls → ∃ C (depending on k only), every expanded description d of a root entry on range n has d.calls ≤ C·(n + 1); reason: a sample follows one description; n + 1 ≤ 2n for n ≥ 1, and n = 0 uses one call
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma D.3, p. 35 (PDF 36)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables

namespace TwMSOCount.Main

theorem lemma_D_3 (k : ℕ) :
    ∃ C : ℕ, ∀ (r : ℕ) [NeZero r] (ψ : Formula r Empty), ψ.IsSentence →
      ∀ (SM : StateMap r k), SM.IsStateMap ψ →
      ∀ (n τ : ℕ) (d : ExpDesc SM (.g ∅ n τ) (Finset.range n)), d.calls ≤ C * (n + 1) := by sorry

end TwMSOCount.Main
