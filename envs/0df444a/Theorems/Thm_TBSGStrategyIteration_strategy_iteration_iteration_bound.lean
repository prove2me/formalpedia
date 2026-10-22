-- Prove2me | Theorems.Thm_TBSGStrategyIteration_strategy_iteration_iteration_bound
-- name    : TBSGStrategyIteration.strategy_iteration_iteration_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:42:01.077971+00:00
-- url     : https://prove2.me/theorems/fe2e0083-20c4-49b5-a50f-7c9b09a2cf66
-- title:
--   Theorem 6.5 — Strategy-Iteration terminates within $(m+1)(1 + \log_{1/\gamma} \frac{n^2}{1-\gamma})$ iterations
-- statement:
--   Let $G$ be a 2-player turn-based discounted stochastic game with $n$ states, $m$ actions (of both players) and discount factor $0 < \gamma < 1$. Let $\tau_2$ map every strategy $\sigma$ of player 1 to an optimal counter-strategy $\tau_2(\sigma)$ of player 2, and let $\sigma^0, \sigma^1, \ldots$ be a run of the Strategy-Iteration algorithm from an arbitrary initial strategy $\sigma^0$: each $\sigma^{k+1}$ is greedy for $v^k = v_{\sigma^k, \tau_2(\sigma^k)}$, with $\sigma^{k+1} = \sigma^k$ whenever $\sigma^k$ is itself greedy. Then the algorithm terminates, and its termination index $N$ (the first $N \ge 1$ with $\sigma^N = \sigma^{N-1}$) satisfies
--   $$N \le (m+1)\Big(1 + \log_{1/\gamma} \frac{n^2}{1-\gamma}\Big),$$
--   and $(\sigma^N, \tau_2(\sigma^N))$ is an optimal strategy profile; in particular $\sigma^N$ is an optimal strategy for player 1.
--
--   For a fixed discount factor this bound is $O\big(\frac{m}{1-\gamma}\log\frac{n}{1-\gamma}\big)$, so strategy iteration is strongly polynomial. With $S_2 = \emptyset$ the game is a Markov decision process, $\tau_2$ is trivial, and the theorem is the bound for Howard's policy iteration.
--
--   **Formalization Note.** Only the explicit bound is stated; the $O(\cdot)$ form is not part of the Lean. The hypothesis on $\tau_2$ is satisfiable by Theorem 2.8. Ties in the greedy step are broken in favour of the current strategy as a whole (clause (b) of `IsRun`), which the paper's per-state rule implies. At $n = 0$ Lean's `Real.logb` returns $0$ and the bound reads $N \le 1$, which holds.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 10, Theorem 6.5

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Theorem 6.5 (Hansen–Miltersen–Zwick): the Strategy-Iteration algorithm, starting from any
initial strategy `σ⁰`, terminates with an optimal strategy after at most
`(m + 1)(1 + log_{1/γ} (n²/(1 − γ)))` iterations, where `n = |S|` and `m = |A|`.
Formally: every run `σ` (Figure 1, with an optimal-counter-strategy map `τ₂` and ties broken in
favour of `σ^k`) has a termination index `N` (the first `N ≥ 1` with `σ^N = σ^{N−1}`) with
`N ≤ (m + 1)(1 + log_{1/γ} (n²/(1 − γ)))`, and `(σ^N, τ₂(σ^N))` is an optimal profile. -/
theorem strategy_iteration_iteration_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ : ℕ → Strat1 G)
    (hrun : IsRun G τ₂ σ) :
    ∃ N : ℕ, IsTerminationIndex σ N ∧
      (N : ℝ) ≤ ((Fintype.card A : ℝ) + 1) *
        (1 + Real.logb (1 / G.γ) ((Fintype.card S : ℝ) ^ 2 / (1 - G.γ))) ∧
      IsOptimal G (σ N, τ₂ (σ N)) := by sorry

end TBSGStrategyIteration
