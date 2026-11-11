-- Prove2me | Theorems.Thm_RankingBeats_General_fact_3_3
-- name    : RankingBeats.General.fact_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:21.551461+00:00
-- url     : https://prove2.me/theorems/a406045f-6c68-4449-b85a-db92da5ba1b6
-- title:
--   Fact 3.3 — u is matched to a vertex of rank ≤ x_v iff u is matched no later than t_uv
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). For every pair of vertices $v\neq u$:
--   $$\big(\exists w:\ (u,w)\in R(\vec x),\ x_w\le x_v\big)\iff\big(\exists w:\ (u,w)\in R(\vec x),\ t_{uw}\le t_{uv}\big),$$
--   i.e. $u$ is matched to a vertex of rank $\le x_v$ iff $u$ is matched at a time no later than $t_{uv}=\min\{(x_u,x_v),(x_v,x_u)\}$ (lexicographic). It translates rank comparisons of matches into the time order of the query-commit view.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 12, Fact 3.3

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_QueryCommit

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 3.3** (p. 12). For every vertex `v ≠ u`, `u` is matched to a vertex of rank `≤ x_v` iff
`u` is matched at a time no later than `t_uv`. -/
theorem fact_3_3 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (u v : V) (hvu : v ≠ u) :
    (∃ w, s(u, w) ∈ ranking G ∅ x ∧ x w ≤ x v) ↔
      (∃ w, s(u, w) ∈ ranking G ∅ x ∧ queryTime x u w ≤ queryTime x u v) := by sorry

end RankingBeats.General
