-- Prove2me | Theorems.Thm_TBSGStrategyIteration_strategy_iteration_geometric
-- name    : TBSGStrategyIteration.strategy_iteration_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:26:41.037452+00:00
-- url     : https://prove2.me/theorems/71b3f62d-ec94-429e-9f7e-b8280cb6fd2f
-- title:
--   Lemma 5.5 — strategy iteration is at least as fast as value iteration
-- statement:
--   Let $\tau_2$ map every player 1 strategy to an optimal counter-strategy, let $\sigma$ be a run of Strategy-Iteration with value vectors $v^k = v_{\sigma^k, \tau_2(\sigma^k)}$, and let $v^* = v_{\pi^*}$ for an optimal profile $\pi^*$. Then for every $k$,
--   $$\|v^k - v^*\|_\infty \le \gamma^k \, \|v^0 - v^*\|_\infty .$$
--
--   **Formalization Note.** The paper states it for $0 \le k \le N$; the Lean statement is for every $k$ (the run is constant, equal to $v^*$, from $N-1$ on).
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 9, Lemma 5.5

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Lemma 5.5: strategy iteration is at least as fast as value iteration: for a run with value
vectors `v^k = v_{σ^k, τ₂(σ^k)}` and the optimal value vector `v* = v_{π*}`,
`‖v^k − v*‖_∞ ≤ γ^k ‖v^0 − v*‖_∞`. Stated for every `k` (the run is constant after it stops). -/
theorem strategy_iteration_geometric {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ : ℕ → Strat1 G)
    (hrun : IsRun G τ₂ σ) (πstar : Profile G) (hstar : IsOptimal G πstar) (k : ℕ) :
    ‖runValue G τ₂ σ k - value G πstar‖ ≤ G.γ ^ k * ‖runValue G τ₂ σ 0 - value G πstar‖ := by sorry

end TBSGStrategyIteration
