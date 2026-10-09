-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_batch_td_converges_to_certainty_equivalence
-- name    : SuttonBartoRL.BatchTD.batch_td_converges_to_certainty_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:00:35.658867+00:00
-- url     : https://prove2.me/theorems/0403bfa3-9271-418e-9a55-0d3191e73f3e
-- title:
--   Batch TD(0) converges to the certainty-equivalence estimate
-- statement:
--   Fix a finite batch of episodes over a finite set $\mathcal S$ of nonterminal states, each ending in the terminal state, and a discount rate $\gamma \in [0, 1]$. Batch-updating TD(0) with step size $\alpha$ from an initial array $V_0$ is the iteration
--
--   $$
--   V_{m+1}(s) = V_m(s) + \alpha \sum_{\text{visits } t \text{ of } s} \big[R_{t+1} + \gamma V_m(S_{t+1}) - V_m(S_t)\big], \qquad V_m(\text{terminal}) = 0 .
--   $$
--
--   Let $\hat v(s) = \sum_{k\ge0}\gamma^k(\hat P^k\hat r)(s)$ be the certainty-equivalence estimate, the value function of the maximum-likelihood Markov reward process of the batch. Then the series defining $\hat v$ converges at every state, and there is $\bar\alpha > 0$, depending only on the batch and $\gamma$, such that for every $\alpha \in (0, \bar\alpha)$, every initial array $V_0$ and every state $s$,
--
--   $$
--   \lim_{m\to\infty} V_m(s) = \begin{cases} \hat v(s) & \text{if } s \text{ is visited in the batch,}\\ V_0(s) & \text{otherwise.}\end{cases}
--   $$
--
--   Under batch updating, TD(0) therefore converges deterministically to a single answer, independent of the step size and of the initialization on visited states, and that answer is the estimate that would be exactly correct if the maximum-likelihood model of the data were the true process.
--
--   **Formalization Note** "As long as $\alpha$ is chosen sufficiently small" is the threshold $\bar\alpha$, quantified before $\alpha$ and $V_0$. Every visit is counted, both in the TD increments and in the model. The undiscounted case $\gamma = 1$ is included; no discounting is needed because every episode ends in the terminal state. Unvisited states receive no increment and keep their initial value, which the statement records explicitly.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §6.3 Optimality of TD(0), p. 126 (batch updating, convergence for sufficiently small α) and p. 128 (certainty-equivalence estimate)

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

open Filter Topology

namespace SuttonBartoRL.BatchTD

/-- §6.3, pp. 126–128: under batch updating, TD(0) converges deterministically to a single answer
independent of the step size `α`, as long as `α` is sufficiently small, and that answer is the
certainty-equivalence estimate. For a finite batch of episodes and `γ ∈ [0, 1]` there is
`ᾱ > 0`, depending only on the batch and `γ`, such that for every `α ∈ (0, ᾱ)` and every initial
array `V₀` the iterates of batch TD(0) converge at every state visited in the batch to the
certainty-equivalence estimate (whose defining series converges); states never visited keep their
initial value. -/
theorem batch_td_converges_to_certainty_equivalence {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ s : S, Summable fun k : ℕ => γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s) ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ (V₀ : S → ℝ) (s : S),
      Tendsto (fun m : ℕ => batchTD α γ b V₀ m s) atTop
        (𝓝 (if visitCount b s = 0 then V₀ s else ceEstimate γ b s)) := by sorry

end SuttonBartoRL.BatchTD
