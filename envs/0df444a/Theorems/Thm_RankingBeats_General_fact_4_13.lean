-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_13
-- name    : RankingBeats.General.fact_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:21.558168+00:00
-- url     : https://prove2.me/theorems/c7cb7252-05f1-41c2-8706-7c2c95787ce4
-- title:
--   Fact 4.13 — demoting u's match v below u's backup rank leaves the matching unchanged
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Let $u$ be matched to $v$ in $R(\vec x)$.
--   - If $u$ has a backup $b$ with respect to $\vec x$, then $R(\vec x)=R(\vec x_{-v}(y))$ for every $y\in[x_v,x_b)$.
--   - If $u$ has no backup, then $R(\vec x)=R(\vec x_{-v}(y))$ for every $y\in[x_v,1)$.
--
--   $$R(\vec x)=R(\vec x_{-v}(y))\qquad (y\in[x_v,x_b)\text{, resp. }y\in[x_v,1)).$$
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11), for x_{-v}(y) → each y carries the hypothesis Function.Injective (Function.update x v y); reason: the paper's standing assumption for the demoted vector
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 16, Fact 4.13

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.13** (Monotonicity of Match Before Backup, p. 16). Let `u` be matched to `v` in
`R(x)`. If `u` has a backup `b` with respect to `x`, then `R(x) = R(x_{-v}(y))` for every
`y ∈ [x_v, x_b)`; if `u` has no backup, then `R(x) = R(x_{-v}(y))` for every `y ∈ [x_v, 1)`. -/
theorem fact_4_13 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (u v : V)
    (huv : s(u, v) ∈ ranking G ∅ x) :
    (∀ b, IsBackup G ∅ x u b → ∀ y ∈ Set.Ico (x v) (x b),
      Function.Injective (Function.update x v y) →
        ranking G ∅ x = ranking G ∅ (Function.update x v y)) ∧
    (¬ HasBackup G ∅ x u → ∀ y ∈ Set.Ico (x v) 1,
      Function.Injective (Function.update x v y) →
        ranking G ∅ x = ranking G ∅ (Function.update x v y)) := by sorry

end RankingBeats.General
