-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_2
-- name    : RankingBeats.General.fact_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:07.138556+00:00
-- url     : https://prove2.me/theorems/8d21e567-452a-44c0-bab8-7ef0ff4cfe34
-- title:
--   Fact 4.2 — a backup has larger rank than the match
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Let $u$ be a vertex matched in $R(\vec x)$ to $v$. If $u$ has a backup $b$ (that is, $(u,b)\in R(\vec x_{-v})$), then
--   $$x_v<x_b.$$
--   Backups are always worse than the current match.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 14, Fact 4.2

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.2** (Backups have Larger Ranks, p. 14). If `u` is matched in `R(x)` to `v` and has a
backup `b`, then `x_v < x_b`. -/
theorem fact_4_2 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (u v b : V)
    (huv : s(u, v) ∈ ranking G ∅ x) (hb : IsBackup G ∅ x u b) :
    x v < x b := by sorry

end RankingBeats.General
