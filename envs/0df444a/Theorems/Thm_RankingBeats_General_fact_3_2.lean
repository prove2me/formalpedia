-- Prove2me | Theorems.Thm_RankingBeats_General_fact_3_2
-- name    : RankingBeats.General.fact_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:15.553473+00:00
-- url     : https://prove2.me/theorems/192bb16a-3179-4ba9-884a-e1225db53860
-- title:
--   Fact 3.2 — Perfect Matching Assumption: a ratio bound on graphs with a perfect matching transfers to all graphs
-- statement:
--   Say that Ranking has approximation ratio at least $\alpha$ on a finite simple graph $H$ if $\mathbb E_{\vec x}[|R_H(\vec x)|]\ge\alpha\cdot\nu(H)$, where the ranks are i.i.d. uniform on $[0,1)$ and $\nu(H)=|\mathrm{OPT}(H)|$ is the maximum matching size. For every real $\alpha$: if Ranking has approximation ratio at least $\alpha$ on every finite simple graph that admits a perfect matching, then it has approximation ratio at least $\alpha$ on every finite simple graph $G$:
--   $$\Big(\forall H\text{ with a perfect matching: } \mathbb E[|R_H(\vec x)|]\ge\alpha\,\nu(H)\Big)\ \Longrightarrow\ \mathbb E[|R_G(\vec x)|]\ge\alpha\,\nu(G).$$
--   This reduction is the first step of the proof of Theorem 1.1 (p. 71).
--
--   Differences from the source:
--   - encoding: 'approximation ratio at least α', α = E_x[|R(x)|] / |OPT| → α · ν(H) ≤ E_x[|R_H(x)|] with ν = StochMatchPoly.mu H.edgeFinset; reason: the form the paper uses (p. 78); it avoids division and covers ν = 0
--   - encoding: all graphs (finite simple graphs on any vertex set) → all SimpleGraph W on vertex types W : Type with Fintype W and a LinearOrder W used as tie-break; reason: every finite vertex set is a type in Type with a linear order; the tie-break affects R only on a null set
--   - encoding: Ranking on rank vectors with distinct ranks (ties have probability zero) → ranking is defined on every x : V → ℝ, with ties broken by a fixed [LinearOrder V]; the vertex type carries such an order; reason: every finite type has a linear order, and the tie-break changes R(x) only on a null set, so the expectation is the paper's
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 11, Fact 3.2 (proof p. 78–79, Appendix B)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_RankingBeats_General_Ranking

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 3.2** (Perfect Matching Assumption, p. 11). If Ranking has approximation ratio at least
`α` on every finite simple graph that admits a perfect matching, i.e. `E_x[|R(x)|] ≥ α · ν`, then
it has approximation ratio at least `α` on every finite simple graph. -/
theorem fact_3_2 (α : ℝ)
    (h : ∀ (W : Type) [Fintype W] [LinearOrder W] (H : SimpleGraph W),
      (∃ M : H.Subgraph, M.IsPerfectMatching) →
        α * (StochMatchPoly.mu H.edgeFinset : ℝ) ≤ expectedSize H)
    (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    α * (StochMatchPoly.mu G.edgeFinset : ℝ) ≤ expectedSize G := by sorry

end RankingBeats.General
