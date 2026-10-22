-- Prove2me | Theorems.Thm_TBSGStrategyIteration_strategy_iteration_correct
-- name    : TBSGStrategyIteration.strategy_iteration_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:22:06.249479+00:00
-- url     : https://prove2.me/theorems/8e5c2bc5-5cce-4aa2-8fcb-6861d0f31b37
-- title:
--   Lemma 5.2 — termination and correctness of Strategy-Iteration
-- statement:
--   Let $\tau_2$ map every player 1 strategy to an optimal counter-strategy against it, and let $\sigma^0, \sigma^1, \ldots$ be a run of Strategy-Iteration with value vectors $v^k = v_{\sigma^k, \tau_2(\sigma^k)}$ and profiles $\pi^k = (\sigma^k, \tau_2(\sigma^k))$. Then the run terminates: it has a termination index $N \ge 1$. Moreover, with $v^*$ the optimal value vector,
--   $$v^{k-1} > v^k \ge v^* \quad (1 \le k < N), \qquad v^{N-1} = v^N = v^*,$$
--   and $\pi^{N-1} = \pi^N$ is an optimal strategy profile. Here $u < v$ means $u \le v$ and $u \ne v$.
--
--   **Formalization Note.** $v^*$ is quantified as $v_{\pi^*}$ for every optimal profile $\pi^*$ (all have the same value, Theorem 2.8). The strict order is written out as $\le$ and $\ne$.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 8, Lemma 5.2

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Lemma 5.2: every run of Strategy-Iteration(σ⁰) terminates: there is a termination index
`N` (`σ^N = σ^{N−1}`, and `σ^k ≠ σ^{k−1}` for `1 ≤ k < N`). With `v^k = v_{σ^k, τ₂(σ^k)}` and
`v*` the optimal value vector (`v_{π*}` for any optimal profile `π*`):
`v^{k−1} > v^k ≥ v*` for every `1 ≤ k < N` (`u < v` means `u ≤ v` and `u ≠ v`, p. 3),
`v^{N−1} = v^N = v*`, and `π^{N−1} = π^N` is an optimal strategy profile. -/
theorem strategy_iteration_correct {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ : ℕ → Strat1 G)
    (hrun : IsRun G τ₂ σ) :
    ∃ N : ℕ, IsTerminationIndex σ N ∧
      (∀ πstar : Profile G, IsOptimal G πstar →
        (∀ k : ℕ, 1 ≤ k → k < N →
          (runValue G τ₂ σ k ≤ runValue G τ₂ σ (k - 1) ∧
              runValue G τ₂ σ k ≠ runValue G τ₂ σ (k - 1)) ∧
            value G πstar ≤ runValue G τ₂ σ k) ∧
        runValue G τ₂ σ (N - 1) = runValue G τ₂ σ N ∧
        runValue G τ₂ σ N = value G πstar) ∧
      ((σ (N - 1), τ₂ (σ (N - 1))) : Profile G) = (σ N, τ₂ (σ N)) ∧
      IsOptimal G (σ N, τ₂ (σ N)) := by sorry

end TBSGStrategyIteration
