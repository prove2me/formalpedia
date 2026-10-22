-- Prove2me | Theorems.Thm_TBSGStrategyIteration_strategy_step_le_valueIterOp
-- name    : TBSGStrategyIteration.strategy_step_le_valueIterOp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:17:19.688341+00:00
-- url     : https://prove2.me/theorems/7ebb1db3-9d7e-461a-8ace-07717af850e6
-- title:
--   Lemma 5.3 — one strategy-iteration step is dominated by one value-iteration step
-- statement:
--   With $\tau_2$, $\pi^0 = (\sigma^0, \tau_2(\sigma^0))$, $\sigma^1$ greedy for $v_{\pi^0}$ and $\pi^1 = (\sigma^1, \tau_2(\sigma^1))$ as in Lemma 5.1,
--   $$\mathcal T v_{\pi^0} \ge v_{\pi^1} .$$
--   Iterating this comparison shows that strategy iteration converges at least as fast as value iteration started from $v_{\pi^0}$.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 9, Lemma 5.3

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Lemma 5.3: with `τ₂`, `π⁰ = (σ⁰, τ₂(σ⁰))`, `σ¹` greedy for `v_{π⁰}` and
`π¹ = (σ¹, τ₂(σ¹))` as in Lemma 5.1, one step of strategy iteration is dominated by one step
of value iteration: `𝒯 v_{π⁰} ≥ v_{π¹}`. -/
theorem strategy_step_le_valueIterOp {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ0 σ1 : Strat1 G)
    (hσ1 : IsGreedy1 G (value G (σ0, τ₂ σ0)) σ1) :
    value G (σ1, τ₂ σ1) ≤ valueIterOp G (value G (σ0, τ₂ σ0)) := by sorry

end TBSGStrategyIteration
