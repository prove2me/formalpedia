-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_bellman_equation_stateValue
-- name    : SuttonBartoRL.FiniteMDP.bellman_equation_stateValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:49:01.670923+00:00
-- url     : https://prove2.me/theorems/d297f33d-1456-4959-b1a0-74c3048e249b
-- title:
--   Eq. (3.14): the Bellman equation for $v_\pi$
-- statement:
--   Let $\pi$ be a stochastic policy for a finite MDP with dynamics $p(s', r \mid s, a)$, and let $0 \le \gamma < 1$. The state-value function $v_\pi$, defined as the expected discounted return (3.12), satisfies for every state $s$
--   $$v_\pi(s) = \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_\pi(s')\big].$$
--
--   This is the Bellman equation for $v_\pi$: the value of a state equals the expected immediate reward plus the discounted value of the expected next state. It is the basis of policy evaluation in the later chapters.
--
--   **Formalization Note** The book states (3.14) also for episodic tasks with $\gamma = 1$; the statement here is for $0 \le \gamma < 1$ (the continuing discounted case, §3.3).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (3.14), p. 59

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Eq. (3.14), p. 59 (the Bellman equation for `v_π`): for a finite MDP,
a stochastic policy `π` and `0 ≤ γ < 1`, the state-value function defined from expected returns
(3.12) satisfies
`v_π(s) = Σ_a π(a|s) Σ_{s',r} p(s', r|s, a) [r + γ v_π(s')]` for all `s`. -/
theorem bellman_equation_stateValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    stateValue M γ π s =
      ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s') := by sorry

end SuttonBartoRL.FiniteMDP
