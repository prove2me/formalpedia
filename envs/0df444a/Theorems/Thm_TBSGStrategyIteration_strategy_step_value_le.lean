-- Prove2me | Theorems.Thm_TBSGStrategyIteration_strategy_step_value_le
-- name    : TBSGStrategyIteration.strategy_step_value_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:12:50.621298+00:00
-- url     : https://prove2.me/theorems/f126f101-7797-415c-becb-1a48d6de3706
-- title:
--   Lemma 5.1 — a strategy-iteration step does not increase values
-- statement:
--   Let $\tau_2$ map every $\sigma \in \Pi_1$ to an optimal counter-strategy $\tau_2(\sigma)$ against $\sigma$. Let $\sigma^0 \in \Pi_1$, $\pi^0 = (\sigma^0, \tau_2(\sigma^0))$, let $\sigma^1$ be greedy for $v_{\pi^0}$ (i.e. $\sigma^1 = \mathcal P_1 v_{\pi^0}$ for some tie-breaking), and $\pi^1 = (\sigma^1, \tau_2(\sigma^1))$. Then
--   $$v_{\pi^0} \ge v_{\pi^1} .$$
--
--   **Formalization Note.** The statement holds for every greedy choice, so no tie-breaking rule is fixed.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 8, Lemma 5.1

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Lemma 5.1: let `τ₂` map every player 1 strategy to an optimal counter-strategy, let
`π⁰ = (σ⁰, τ₂(σ⁰))`, let `σ¹` be any value of `𝒫₁ v_{π⁰}` (greedy for `v_{π⁰}`) and
`π¹ = (σ¹, τ₂(σ¹))`. Then `v_{π⁰} ≥ v_{π¹}`. -/
theorem strategy_step_value_le {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ0 σ1 : Strat1 G)
    (hσ1 : IsGreedy1 G (value G (σ0, τ₂ σ0)) σ1) :
    value G (σ1, τ₂ σ1) ≤ value G (σ0, τ₂ σ0) := by sorry

end TBSGStrategyIteration
