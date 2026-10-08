-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_policy_improvement_theorem
-- name    : SuttonBartoRL.DP.policy_improvement_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:51:18.620002+00:00
-- url     : https://prove2.me/theorems/51739bb8-a3ee-4c7c-9fee-116f049a1ec1
-- title:
--   Policy improvement theorem (4.7)–(4.8)
-- statement:
--   Let a finite MDP with discount rate $0 \le \gamma < 1$ be given, and let $\pi$ and $\pi'$ be any pair of deterministic policies such that, for all $s \in \mathcal S$,
--   $$
--   q_\pi(s, \pi'(s)) \;\ge\; v_\pi(s). \tag{4.7}
--   $$
--   Then $\pi'$ is as good as, or better than, $\pi$: it obtains greater or equal expected return from every state,
--   $$
--   v_{\pi'}(s) \;\ge\; v_\pi(s) \qquad \text{for all } s \in \mathcal S. \tag{4.8}
--   $$
--   Moreover, at every state $s$ where (4.7) is strict, (4.8) is strict at that same state.
--
--   Here $v_\pi(s)$ is the expected discounted return from $s$ under $\pi$ and $q_\pi(s,a) = \sum_{s',r} p(s',r\mid s,a)\,[r+\gamma v_\pi(s')]$ is the value of taking $a$ once in $s$ and following $\pi$ thereafter (4.6).
--
--   The theorem is the basis of policy improvement and policy iteration: a local one-step comparison against $v_\pi$ certifies a global improvement.
--
--   **Formalization Note** The book also allows $\gamma = 1$ with guaranteed termination (p. 74) but never states the termination hypothesis precisely; this statement is for $0 \le \gamma < 1$ (continuing tasks, no terminal state). $v_\pi$ is defined from expected returns, not from the Bellman equation, and a deterministic policy is the stochastic policy that selects $\pi(s)$ with probability one.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, policy improvement theorem (4.7)–(4.8), with (4.6), p. 78

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Policy improvement theorem, Sutton & Barto (2018), (4.7)–(4.8), p. 78. Let `π` and `π'` be
deterministic policies with `q_π(s, π'(s)) ≥ v_π(s)` for all `s` (4.7). Then
`v_{π'}(s) ≥ v_π(s)` for all `s` (4.8), and wherever (4.7) is strict, (4.8) is strict at the same
state. Values are expected discounted returns with `0 ≤ γ < 1`; `q_π` is defined by (4.6). -/
theorem policy_improvement_theorem {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : S → A)
    (h47 : ∀ s, stateValue M γ (Policy.ofDet π) s ≤
      actionValue M γ (Policy.ofDet π) s (π' s)) :
    (∀ s, stateValue M γ (Policy.ofDet π) s ≤ stateValue M γ (Policy.ofDet π') s) ∧
    (∀ s, stateValue M γ (Policy.ofDet π) s < actionValue M γ (Policy.ofDet π) s (π' s) →
      stateValue M γ (Policy.ofDet π) s < stateValue M γ (Policy.ofDet π') s) := by sorry

end SuttonBartoRL.DP
