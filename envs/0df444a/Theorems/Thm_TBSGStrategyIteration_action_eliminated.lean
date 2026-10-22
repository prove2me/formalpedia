-- Prove2me | Theorems.Thm_TBSGStrategyIteration_action_eliminated
-- name    : TBSGStrategyIteration.action_eliminated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:38:10.782305+00:00
-- url     : https://prove2.me/theorems/ee3cff3e-9198-4529-9b9b-412825b26c90
-- title:
--   Lemma 6.4 (corrected) — every $L$ iterations an action is eliminated for good
-- statement:
--   Let $\tau_2$ map every player 1 strategy to an optimal counter-strategy, let $\sigma$ be a run of Strategy-Iteration with termination index $N$, and let
--   $$L = \log_{1/\gamma} \frac{n^2}{1-\gamma} .$$
--   Then for every $k$ with $k + 1 < N$, the strategy $\sigma^k$ contains an action $\sigma^k(i)$, $i \in S_1$, that does not appear in any strategy $\sigma^\ell$ with $k + L < \ell \le N$.
--
--   **Formalization Note (correction).** The printed lemma asserts this for every $k \le N$. That is false for $k = N-1$: $\sigma^N = \sigma^{N-1}$, and $\ell = N$ lies in the range $k + L < \ell \le N$ whenever $L < 1$ (e.g. one state, two self-loop actions of costs $0$ and $1$, $\gamma = 0.3$, $\sigma^0$ the cost-$0$ action: $N = 1$, $L \approx 0.30$). The paper's proof needs $\pi^k$ non-optimal, which holds exactly when $k + 1 < N$ (Lemma 5.2); the Lean statement adds that hypothesis. The main theorem only uses the lemma for such $k$. `Real.logb` is applied with base $1/\gamma > 1$; for $n \ge 1$ its argument is positive.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 10, Lemma 6.4 (corrected: hypothesis k + 1 < N added)

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal
import Definitions.Def_TBSGStrategyIteration_IsRun

namespace TBSGStrategyIteration

/-- Lemma 6.4, corrected: let `σ` be a run of Strategy-Iteration with termination index `N`
and `L = log_{1/γ} (n²/(1 − γ))`. Then every strategy `σ^k` with `k + 1 < N` contains an action
that appears in no strategy `σ^ℓ` with `k + L < ℓ ≤ N`.
Correction: the printed lemma claims this for every `k ≤ N`; it is false for `k = N − 1`,
`ℓ = N` whenever `L < 1` (then `σ^N = σ^{N−1}`). The proof uses that `π^k` is not optimal,
which holds exactly for `k + 1 < N` (Lemma 5.2). -/
theorem action_eliminated {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (τ₂ : Strat1 G → Strat2 G)
    (hτ : ∀ σ : Strat1 G, IsOptCounter2 G σ (τ₂ σ)) (σ : ℕ → Strat1 G)
    (hrun : IsRun G τ₂ σ) (N : ℕ) (hN : IsTerminationIndex σ N) (k : ℕ) (hk : k + 1 < N) :
    ∃ i : {i : S // i ∈ G.S1}, ∀ ℓ : ℕ,
      (k : ℝ) + Real.logb (1 / G.γ) ((Fintype.card S : ℝ) ^ 2 / (1 - G.γ)) < ℓ → ℓ ≤ N →
        ∀ i' : {i : S // i ∈ G.S1}, (σ ℓ).act i' ≠ (σ k).act i := by sorry

end TBSGStrategyIteration
