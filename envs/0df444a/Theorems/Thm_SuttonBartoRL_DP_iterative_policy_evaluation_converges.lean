-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_iterative_policy_evaluation_converges
-- name    : SuttonBartoRL.DP.iterative_policy_evaluation_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:50:54.216172+00:00
-- url     : https://prove2.me/theorems/af0e0149-c65f-4348-9366-2bd99e27ade5
-- title:
--   Iterative policy evaluation (4.5) converges to $v_\pi$
-- statement:
--   Let $\pi$ be any policy of a finite MDP with discount rate $0 \le \gamma < 1$, and let $v_0 : \mathcal S \to \mathbb R$ be arbitrary. Define successive approximations by the update (4.5):
--   $$
--   v_{k+1}(s) \;=\; \sum_a \pi(a\mid s) \sum_{s', r} p(s', r\mid s, a)\,\big[r + \gamma v_k(s')\big], \qquad s \in \mathcal S .
--   $$
--   Then $v_k(s) \to v_\pi(s)$ as $k \to \infty$ for every state $s$, where $v_\pi$ is the expected discounted return of $\pi$.
--
--   This justifies iterative policy evaluation, the evaluation step of policy iteration.
--
--   **Formalization Note** The book's condition "either $\gamma < 1$ or eventual termination is guaranteed from all states under $\pi$" (p. 74) is formalized in the case $\gamma < 1$ only; the book never states the termination hypothesis precisely. Convergence is in the product topology on $\mathbb R^{\mathcal S}$, which for finite $\mathcal S$ is the same as convergence in the sup norm.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (4.5) and the paragraph after it, p. 74

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Iterative policy evaluation, Sutton & Barto (2018), (4.5), p. 74: for `0 ≤ γ < 1`, any policy
`π` and any initial approximation `v_0 : S → ℝ`, the iterates `v_{k+1} = evalUpdate v_k` of (4.5)
converge to `v_π` as `k → ∞`. -/
theorem iterative_policy_evaluation_converges {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : Policy S A)
    (v₀ : S → ℝ) :
    Filter.Tendsto (fun k : ℕ => (evalUpdate M γ π)^[k] v₀) Filter.atTop
      (nhds (stateValue M γ π)) := by sorry

end SuttonBartoRL.DP
