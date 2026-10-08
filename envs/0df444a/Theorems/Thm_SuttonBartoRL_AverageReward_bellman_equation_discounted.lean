-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_bellman_equation_discounted
-- name    : SuttonBartoRL.AverageReward.bellman_equation_discounted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:40:23.366978+00:00
-- url     : https://prove2.me/theorems/9c1f9e1b-c90d-4860-b5f7-141ee263166f
-- title:
--   (3.14): the Bellman equation for the discounted value $v^\gamma_\pi$
-- statement:
--   Let $\pi$ be a policy in a finite MDP and $0 \le \gamma < 1$. The discounted value function $v^\gamma_\pi(s) = \mathbb E_\pi[\sum_{k\ge 0}\gamma^k R_{t+k+1}\mid S_t = s]$ satisfies, for every state $s$,
--   $$
--   v^\gamma_\pi(s) = \sum_a \pi(a\mid s)\sum_{s', r} p(s', r\mid s, a)\big[r + \gamma\, v^\gamma_\pi(s')\big].
--   $$
--
--   This is the step labelled "(Bellman Eq.)" in the box *The Futility of Discounting in Continuing Problems*.
--
--   **Formalization Note** $v^\gamma_\pi$ is defined from expected returns as a series, so this equation is a theorem about that series, not a definition.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (3.14), p. 59; used as "(Bellman Eq.)" in the box on p. 254

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), (3.14), p. 59, the step "(Bellman Eq.)" of the box on p. 254: for
`0 ≤ γ < 1` the return-defined discounted value function satisfies
`v^γ_π(s) = Σ_a π(a | s) Σ_{s', r} p(s', r | s, a) [r + γ v^γ_π(s')]` for all `s ∈ S`. -/
theorem bellman_equation_discounted {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    M.stateValue γ π s =
      ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * M.stateValue γ π s') := by sorry

end SuttonBartoRL.AverageReward
