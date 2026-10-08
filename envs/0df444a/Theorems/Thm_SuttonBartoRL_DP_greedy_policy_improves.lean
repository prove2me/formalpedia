-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_greedy_policy_improves
-- name    : SuttonBartoRL.DP.greedy_policy_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:58.812783+00:00
-- url     : https://prove2.me/theorems/96bd5990-4fcf-4712-a1a0-741065cc0534
-- title:
--   The greedy policy (4.9) satisfies (4.7) and improves on $\pi$
-- statement:
--   Let $\pi$ be a deterministic policy of a finite MDP with discount $0 \le \gamma < 1$, and let $\pi'$ be a deterministic policy that is greedy with respect to $q_\pi$:
--   $$
--   \pi'(s) \in \operatorname*{argmax}_a q_\pi(s,a) = \operatorname*{argmax}_a \sum_{s',r} p(s',r\mid s,a)\,\big[r+\gamma v_\pi(s')\big] \qquad \text{for all } s,
--   $$
--   with ties broken arbitrarily. Then
--
--   1. $\pi'$ meets the condition (4.7) of the policy improvement theorem: $q_\pi(s, \pi'(s)) \ge v_\pi(s)$ for all $s$;
--   2. $\pi'$ is as good as, or better than, $\pi$: $v_{\pi'}(s) \ge v_\pi(s)$ for all $s$.
--
--   This is the policy improvement step of policy iteration.
--
--   **Formalization Note** Values are expected discounted returns with $0\le\gamma<1$; $q_\pi$ is defined by (4.6). A deterministic policy is identified with the stochastic policy selecting $\pi(s)$ with probability one.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (4.9) and the paragraph after it, p. 79

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Greedy policy improvement, Sutton & Barto (2018), (4.9), p. 79: if the deterministic policy
`π'` is greedy with respect to `q_π` for a deterministic policy `π`, then `π'` meets the
condition (4.7), `q_π(s, π'(s)) ≥ v_π(s)` for all `s`, and it is as good as or better than `π`:
`v_{π'}(s) ≥ v_π(s)` for all `s`. -/
theorem greedy_policy_improves {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π π' : S → A)
    (hgreedy : IsGreedy M γ (Policy.ofDet π) π') :
    (∀ s, stateValue M γ (Policy.ofDet π) s ≤ actionValue M γ (Policy.ofDet π) s (π' s)) ∧
    (∀ s, stateValue M γ (Policy.ofDet π) s ≤ stateValue M γ (Policy.ofDet π') s) := by sorry

end SuttonBartoRL.DP
