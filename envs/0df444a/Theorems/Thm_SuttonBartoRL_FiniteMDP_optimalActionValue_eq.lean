-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_optimalActionValue_eq
-- name    : SuttonBartoRL.FiniteMDP.optimalActionValue_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:51:01.549078+00:00
-- url     : https://prove2.me/theorems/64e7543f-b515-4927-acca-0267ca6a6fa1
-- title:
--   Eq. (3.17): $q_*(s,a) = \mathbb E[R_{t+1} + \gamma v_*(S_{t+1}) \mid S_t=s, A_t=a]$
-- statement:
--   Let $0 \le \gamma < 1$ and consider a finite MDP with a nonempty action set. For every state $s$ and action $a$, the maximum
--   $$q_*(s, a) = \max_\pi q_\pi(s, a) \qquad (3.16)$$
--   over stochastic policies is attained, and
--   $$q_*(s, a) = \mathbb E[R_{t+1} + \gamma v_*(S_{t+1}) \mid S_t = s, A_t = a] = \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_*(s')\big],$$
--   where $v_*(s) = \max_\pi v_\pi(s)$ is the optimal state-value function (3.15).
--
--   The optimal value of an action is its expected immediate reward plus the discounted optimal value of the next state: after the first action, an optimal policy is followed.
--
--   **Formalization Note** The book writes the conditional expectation (3.17); the statement uses its finite-sum form over next states and rewards. The attainment of the maximum is part of the statement, so $q_*$ is the book's maximum and not a junk value of a Lean supremum.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.16)–(3.17), p. 63

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Eqs. (3.16)–(3.17), p. 63: for `0 ≤ γ < 1` and every state–action pair,
the maximum `q_*(s, a) = max_π q_π(s, a)` over stochastic policies is attained, and
`q_*(s, a) = E[R_{t+1} + γ v_*(S_{t+1}) | S_t = s, A_t = a] = Σ_{s',r} p(s', r|s, a) [r + γ v_*(s')]`,
where `v_*(s) = max_π v_π(s)` (3.15). -/
theorem optimalActionValue_eq {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    IsGreatest (Set.range fun π : Policy S A => actionValue M γ π s a)
        (optimalActionValue M γ s a) ∧
      optimalActionValue M γ s a =
        ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * optimalValue M γ s') := by sorry

end SuttonBartoRL.FiniteMDP
