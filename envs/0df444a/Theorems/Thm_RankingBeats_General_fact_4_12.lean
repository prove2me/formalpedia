-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_12
-- name    : RankingBeats.General.fact_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:17.175194+00:00
-- url     : https://prove2.me/theorems/9ea8115a-1878-440b-8daa-97306c404cf4
-- title:
--   Fact 4.12 — demoting a vertex's rank can only worsen its match
-- statement:
--   $G=(V,E)$ is a finite simple graph. Fix a vertex $v$, a rank vector $\vec x_{-v}$ (ranks in $[0,1)$) and two ranks $a<b$ in $[0,1)$, with all ranks of $\vec x_{-v}(a)$ pairwise distinct and all ranks of $\vec x_{-v}(b)$ pairwise distinct.
--   - If $v$ is unmatched in $R(\vec x_{-v}(a))$, then it is also unmatched in $R(\vec x_{-v}(b))$.
--   - If $v$ is matched to a vertex of rank $x_w$ in $R(\vec x_{-v}(a))$, then its match in $R(\vec x_{-v}(b))$, if it is matched at all, has rank $\ge x_w$.
--
--   $$(v,w)\in R(\vec x_{-v}(a)),\ (v,w')\in R(\vec x_{-v}(b))\ \Longrightarrow\ x_w\le x_{w'}.$$
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11), for x_{-v}(x) and x_{-v}(y) → hypotheses Function.Injective (Function.update x v a) and Function.Injective (Function.update x v b); the paper's ranks x < y are named a < b; reason: the paper's standing assumption, made explicit binders
--   - encoding: a rank vector x_{-v} on V \ {v} → a full vector x : V → ℝ whose v-coordinate is ignored (only Function.update x v a and Function.update x v b are run); hx also asks x v ∈ [0, 1); reason: every x_{-v} extends to such an x
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 16, Fact 4.12

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.12** (Worse Vertex has Worse Match, p. 16). Fix `v` and `x_{-v}`, and ranks `a < b`
in `[0, 1)`. If `v` is unmatched in `R(x_{-v}(a))`, it is unmatched in `R(x_{-v}(b))`; if `v` is
matched to a vertex of rank `x_w` in `R(x_{-v}(a))`, its match in `R(x_{-v}(b))` (if any) has rank
`≥ x_w`. -/
theorem fact_4_12 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (v : V)
    (x : V → ℝ) (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (a b : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1)
    (hb : b ∈ Set.Ico (0 : ℝ) 1) (hab : a < b)
    (hinja : Function.Injective (Function.update x v a))
    (hinjb : Function.Injective (Function.update x v b)) :
    (¬ IsMatched (ranking G ∅ (Function.update x v a)) v →
      ¬ IsMatched (ranking G ∅ (Function.update x v b)) v) ∧
    (∀ w, s(v, w) ∈ ranking G ∅ (Function.update x v a) →
      ∀ w', s(v, w') ∈ ranking G ∅ (Function.update x v b) → x w ≤ x w') := by sorry

end RankingBeats.General
