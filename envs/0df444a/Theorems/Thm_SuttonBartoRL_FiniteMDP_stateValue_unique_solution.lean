-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_stateValue_unique_solution
-- name    : SuttonBartoRL.FiniteMDP.stateValue_unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:49:24.762086+00:00
-- url     : https://prove2.me/theorems/0b327ec4-f40d-4fa6-b126-838841323df2
-- title:
--   $v_\pi$ is the unique solution of its Bellman equation (3.14)
-- statement:
--   Let $\pi$ be a stochastic policy for a finite MDP and $0 \le \gamma < 1$. If a function $v$ on the states satisfies, for every state $s$,
--   $$v(s) = \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\big[r + \gamma v(s')\big],$$
--   then $v = v_\pi$, the state-value function (3.12).
--
--   Together with (3.14) this says that the value function $v_\pi$ is the unique solution to its Bellman equation, so that $v_\pi$ can be computed by solving a linear system (as the book does for the gridworld of Example 3.5).
--
--   **Formalization Note** For $\gamma = 1$ uniqueness needs termination of every episode, which the book does not state; the statement is for $0 \le \gamma < 1$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §3.5, p. 60 ("The value function v_π is the unique solution to its Bellman equation")

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP
import Definitions.Def_SuttonBartoRL_FiniteMDP_ValueFunctions

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., p. 60: "The value function `v_π` is the unique solution to its Bellman
equation." For `0 ≤ γ < 1`, every function `v : S → ℝ` satisfying (3.14),
`v(s) = Σ_a π(a|s) Σ_{s',r} p(s', r|s, a) [r + γ v(s')]` for all `s`, equals `v_π`. -/
theorem stateValue_unique_solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A) (v : S → ℝ)
    (hv : ∀ s, v s = ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s')) :
    v = stateValue M γ π := by sorry

end SuttonBartoRL.FiniteMDP
