-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_stateValue_eq_sum_actionValue
-- name    : SuttonBartoRL.FiniteMDP.stateValue_eq_sum_actionValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:49:49.458334+00:00
-- url     : https://prove2.me/theorems/f4a9646e-0b26-4b0f-9e3e-0ed4c9275305
-- title:
--   Exercise 3.18: $v_\pi(s) = \sum_a \pi(a|s)\, q_\pi(s,a)$
-- statement:
--   Let $\pi$ be a stochastic policy for a finite MDP and $0 \le \gamma < 1$. For every state $s$,
--   $$v_\pi(s) = \mathbb E_\pi[q_\pi(S_t, A_t) \mid S_t = s] = \sum_a \pi(a \mid s)\, q_\pi(s, a),$$
--   where $v_\pi$ and $q_\pi$ are the state- and action-value functions (3.12)–(3.13).
--
--   The value of a state is the policy-weighted average of the values of the actions available in it. Chapter 13 uses this identity in the proof of the policy gradient theorem.
--
--   **Formalization Note** The book asks for this equation and prints none; the displayed identity is the formalization's answer.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 3.18, p. 62 (the book gives no solution)

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Exercise 3.18, p. 62 (the book gives no solution): for `0 ≤ γ < 1`,
`v_π(s) = E_π[q_π(S_t, A_t) | S_t = s] = Σ_a π(a|s) q_π(s, a)`. -/
theorem stateValue_eq_sum_actionValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (s : S) :
    stateValue M γ π s = ∑ a, π.prob s a * actionValue M γ π s a := by sorry

end SuttonBartoRL.FiniteMDP
