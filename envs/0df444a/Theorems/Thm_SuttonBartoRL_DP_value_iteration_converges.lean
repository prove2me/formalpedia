-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_value_iteration_converges
-- name    : SuttonBartoRL.DP.value_iteration_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:51:33.271078+00:00
-- url     : https://prove2.me/theorems/cab01c66-cba4-4f8d-9256-79e8bd8f3922
-- title:
--   Value iteration (4.10) converges to $v_*$
-- statement:
--   Let a finite MDP with discount $0 \le \gamma < 1$ be given, and let $v_0 : \mathcal S \to \mathbb R$ be arbitrary. Define
--   $$
--   v_{k+1}(s) \;=\; \max_a \sum_{s',r} p(s',r\mid s,a)\,\big[r+\gamma v_k(s')\big], \qquad s \in \mathcal S .
--   $$
--   Then the optimal value $v_*(s) = \max_\pi v_\pi(s)$ is attained by a single policy $\pi$ simultaneously at every state, and $v_k(s) \to v_*(s)$ as $k \to \infty$ for every $s$.
--
--   This is the convergence guarantee of value iteration.
--
--   **Formalization Note** The book's "under the same conditions that guarantee the existence of $v_*$" is formalized as $\gamma < 1$. $v_*$ is the supremum over all stochastic policies of the expected discounted return, not a fixed point assumed to exist.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (4.10) and the sentence after it, p. 83

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Value iteration, Sutton & Barto (2018), (4.10), p. 83: for `0 ≤ γ < 1` and arbitrary
`v_0 : S → ℝ`, the iterates `v_{k+1}(s) = max_a Σ_{s', r} p(s', r | s, a) [r + γ v_k(s')]` converge
to the optimal value function `v_*(s) = max_π v_π(s)`, and that maximum over policies is attained. -/
theorem value_iteration_converges {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v₀ : S → ℝ) :
    (∃ π : Policy S A, ∀ s, stateValue M γ π s = optimalValue M γ s) ∧
    Filter.Tendsto (fun k : ℕ => (valueIterUpdate M γ)^[k] v₀) Filter.atTop
      (nhds (optimalValue M γ)) := by sorry

end SuttonBartoRL.DP
