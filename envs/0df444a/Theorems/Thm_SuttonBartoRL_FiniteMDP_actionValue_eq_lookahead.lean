-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_actionValue_eq_lookahead
-- name    : SuttonBartoRL.FiniteMDP.actionValue_eq_lookahead
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:50:01.078228+00:00
-- url     : https://prove2.me/theorems/4aaa6cc7-0767-45a3-ad5a-fbbc2252db97
-- title:
--   Exercise 3.19: $q_\pi(s,a) = \sum_{s',r} p(s',r|s,a)[r + \gamma v_\pi(s')]$
-- statement:
--   Let $\pi$ be a stochastic policy for a finite MDP and $0 \le \gamma < 1$. For every state $s$ and action $a$,
--   $$q_\pi(s, a) = \mathbb E[R_{t+1} + \gamma v_\pi(S_{t+1}) \mid S_t = s, A_t = a] = \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v_\pi(s')\big].$$
--
--   The value of an action is the expected immediate reward plus the discounted value of the next state under $\pi$. With Exercise 3.18 it gives the Bellman equation (3.14); Chapter 13 uses it in the proof of the policy gradient theorem.
--
--   **Formalization Note** The book asks for this equation and prints none; the displayed identity is the formalization's answer.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 3.19, p. 62 (the book gives no solution)

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Exercise 3.19, p. 62 (the book gives no solution): for `0 ≤ γ < 1`,
`q_π(s, a) = E[R_{t+1} + γ v_π(S_{t+1}) | S_t = s, A_t = a] = Σ_{s',r} p(s', r|s, a) [r + γ v_π(s')]`. -/
theorem actionValue_eq_lookahead {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) (a : A) :
    actionValue M γ π s a = ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ π s') := by sorry

end SuttonBartoRL.FiniteMDP
