-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_batch_td_fixed_point_iff_certainty_equivalence
-- name    : SuttonBartoRL.BatchTD.batch_td_fixed_point_iff_certainty_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:00:28.471238+00:00
-- url     : https://prove2.me/theorems/8f082ecf-b9e6-4757-bfd8-ba436cb3f608
-- title:
--   Batch TD(0) fixed points are exactly the certainty-equivalence estimate
-- statement:
--   Fix a finite batch of episodes over a finite set $\mathcal S$ of nonterminal states, each ending in the terminal state, and $\gamma \in [0, 1]$. Let $\hat P$, $\hat r$ be the maximum-likelihood Markov reward process of the batch and
--
--   $$
--   \hat v(s) = \sum_{k \ge 0} \gamma^k (\hat P^k \hat r)(s)
--   $$
--
--   its value function, the certainty-equivalence estimate. Then:
--
--   1. the series defining $\hat v(s)$ converges at every $s \in \mathcal S$;
--   2. for every array $V$, the batch TD(0) increment $\sum_{\text{visits } t \text{ of } s}[R_{t+1} + \gamma V(S_{t+1}) - V(S_t)]$ vanishes at every state if and only if $V(s) = \hat v(s)$ for every state $s$ visited in the batch.
--
--   This is the statement that batch TD(0) finds the estimates that would be exactly correct for the maximum-likelihood model: the answer of batch TD(0) is characterized without reference to $\alpha$.
--
--   **Formalization Note** The case $\gamma = 1$ (used in Example 6.4) is included; no hypothesis on the batch beyond finiteness is made, because every episode ends in the terminal state by construction. Values at unvisited states are unconstrained, as they receive no increment.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §6.3, p. 128

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

namespace SuttonBartoRL.BatchTD

/-- §6.3, p. 128: batch TD(0) "always finds the estimates that would be exactly correct for the
maximum-likelihood model of the Markov process". For `γ ∈ [0, 1]`, the series defining the
certainty-equivalence estimate converges at every state, and an array `V` is a fixed point of
batch TD(0) (the sum of all increments vanishes at every state) iff `V` agrees with the
certainty-equivalence estimate on every state visited in the batch. -/
theorem batch_td_fixed_point_iff_certainty_equivalence {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ s : S, Summable fun k : ℕ => γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s) ∧
    ∀ V : S → ℝ,
      (∀ s : S, tdIncrement γ b V s = 0) ↔
        ∀ s : S, visitCount b s ≠ 0 → V s = ceEstimate γ b s := by sorry

end SuttonBartoRL.BatchTD
