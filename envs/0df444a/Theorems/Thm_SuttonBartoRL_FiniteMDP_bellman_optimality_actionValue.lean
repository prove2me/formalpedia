-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_bellman_optimality_actionValue
-- name    : SuttonBartoRL.FiniteMDP.bellman_optimality_actionValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:50:15.467474+00:00
-- url     : https://prove2.me/theorems/7bff4fb9-ff0f-4bed-af57-1a8ae08bc57d
-- title:
--   Eq. (3.20): the Bellman optimality equation for $q_*$
-- statement:
--   Let $0 \le \gamma < 1$ and consider a finite MDP with a nonempty action set. The optimal action-value function $q_*(s, a) = \max_\pi q_\pi(s, a)$ satisfies, for every state $s$ and action $a$,
--   $$q_*(s, a) = \sum_{s', r} p(s', r \mid s, a)\Big[r + \gamma \max_{a'} q_*(s', a')\Big].$$
--
--   This is the Bellman optimality equation for action values: it expresses $q_*$ without reference to any particular policy, and it is the fixed-point equation behind Q-learning.
--
--   **Formalization Note** The book also writes the equation as a conditional expectation; the statement uses the finite-sum form. The maximum over $a'$ is a maximum over the finite nonempty action set.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (3.20), p. 64

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Eq. (3.20), p. 64 (the Bellman optimality equation for `q_*`): for
`0 ≤ γ < 1`, `q_*(s, a) = Σ_{s',r} p(s', r|s, a) [r + γ max_{a'} q_*(s', a')]` for all `s`, `a`. -/
theorem bellman_optimality_actionValue {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    optimalActionValue M γ s a =
      ∑ s', ∑ r ∈ M.R, M.p s a s' r *
        (r + γ * Finset.univ.sup' Finset.univ_nonempty (fun a' => optimalActionValue M γ s' a')) := by sorry

end SuttonBartoRL.FiniteMDP
