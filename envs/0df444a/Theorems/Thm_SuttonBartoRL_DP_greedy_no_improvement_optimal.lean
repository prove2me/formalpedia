-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_greedy_no_improvement_optimal
-- name    : SuttonBartoRL.DP.greedy_no_improvement_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:51:11.398916+00:00
-- url     : https://prove2.me/theorems/0963185c-e47f-40e4-9770-46463d89c8d8
-- title:
--   If the greedy policy is no better, both policies are optimal
-- statement:
--   Let $\pi$ be a deterministic policy of a finite MDP with discount $0 \le \gamma < 1$, and let $\pi'$ be a deterministic policy greedy with respect to $q_\pi$ (4.9). Suppose $\pi'$ is as good as, but not better than, $\pi$, i.e. $v_{\pi'} = v_\pi$. Then
--
--   1. $v_{\pi'}$ satisfies the Bellman optimality equation (4.1): for all $s$,
--   $$
--   v_{\pi'}(s) \;=\; \max_a \sum_{s',r} p(s',r\mid s,a)\,\big[r+\gamma v_{\pi'}(s')\big];
--   $$
--   2. $v_{\pi'} = v_*$, the optimal value function;
--   3. both $\pi$ and $\pi'$ are optimal policies.
--
--   Consequently policy improvement yields a strictly better policy unless the original policy is already optimal.
--
--   **Formalization Note** Optimality is with respect to all stochastic policies, and $v_*(s)$ is the supremum of $v_\pi(s)$ over all stochastic policies.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §4.2, p. 79 (paragraph after (4.9))

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Sutton & Barto (2018), p. 79: if the deterministic policy `π'` is greedy with respect to
`q_π` and is as good as, but not better than, the deterministic policy `π` (`v_{π'} = v_π`),
then `v_{π'}` satisfies the Bellman optimality equation (4.1),
`v_{π'}(s) = max_a Σ_{s', r} p(s', r | s, a) [r + γ v_{π'}(s')]`, `v_{π'} = v_*`, and both `π` and
`π'` are optimal policies. -/
theorem greedy_no_improvement_optimal {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π π' : S → A) (hgreedy : IsGreedy M γ (Policy.ofDet π) π')
    (heq : ∀ s, stateValue M γ (Policy.ofDet π') s = stateValue M γ (Policy.ofDet π) s) :
    (∀ s, stateValue M γ (Policy.ofDet π') s =
      Finset.univ.sup' Finset.univ_nonempty (fun a : A =>
        ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * stateValue M γ (Policy.ofDet π') s'))) ∧
    (∀ s, stateValue M γ (Policy.ofDet π') s = optimalValue M γ s) ∧
    IsOptimalPolicy M γ (Policy.ofDet π) ∧ IsOptimalPolicy M γ (Policy.ofDet π') := by sorry

end SuttonBartoRL.DP
