-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_stateValue_shiftRewards
-- name    : SuttonBartoRL.FiniteMDP.stateValue_shiftRewards
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:49:39.999714+00:00
-- url     : https://prove2.me/theorems/bb2531ce-6930-4394-b9bc-cbc1e0821ee6
-- title:
--   Exercise 3.15: adding $c$ to every reward adds $c/(1-\gamma)$ to every value
-- statement:
--   Let $0 \le \gamma < 1$, let $c$ be a real constant, and consider the MDP obtained from a finite MDP by adding $c$ to every reward (same states, actions and transitions; the reward $r$ becomes $r + c$). For every policy $\pi$ and every state $s$, the state value in the modified MDP is
--   $$v'_\pi(s) = v_\pi(s) + v_c, \qquad v_c = \frac{c}{1 - \gamma}.$$
--
--   In particular the constant shift is the same for all states and all policies, so it does not affect the relative values of any states under any policies.
--
--   **Formalization Note** The book asks for this proof and for $v_c$ in terms of $c$ and $\gamma$, and prints no solution; $v_c = c/(1-\gamma)$ is the formalization's answer, obtained from (3.10). The statement is for the continuing discounted case, the one the exercise addresses.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 3.15, p. 61 (the book gives no solution)

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Exercise 3.15, p. 61 (the book gives no solution): for `0 ≤ γ < 1`,
adding a constant `c` to all rewards adds the same constant `v_c = c / (1 − γ)` to the value of
every state under every policy. -/
theorem stateValue_shiftRewards {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : ℝ) (π : Policy S A) (s : S) :
    stateValue (M.shiftRewards c) γ π s = stateValue M γ π s + c / (1 - γ) := by sorry

end SuttonBartoRL.FiniteMDP
