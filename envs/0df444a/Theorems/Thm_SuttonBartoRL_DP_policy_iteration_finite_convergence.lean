-- Prove2me | Theorems.Thm_SuttonBartoRL_DP_policy_iteration_finite_convergence
-- name    : SuttonBartoRL.DP.policy_iteration_finite_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:51:22.694505+00:00
-- url     : https://prove2.me/theorems/2d87508b-bf61-4dab-af4e-a5c0869b8bbe
-- title:
--   Policy iteration reaches an optimal policy in finitely many iterations
-- statement:
--   Let $\pi_0, \pi_1, \pi_2, \dots$ be deterministic policies of a finite MDP with discount $0 \le \gamma < 1$ such that each $\pi_{k+1}$ is greedy with respect to $q_{\pi_k}$ (4.9), ties broken arbitrarily. Then
--
--   1. each policy is a strict improvement over the previous one unless it is already optimal: for every $k$, either $\pi_k$ is optimal, or $v_{\pi_{k+1}}(s) \ge v_{\pi_k}(s)$ for all $s$ with strict inequality at some state;
--   2. the process reaches an optimal policy and the optimal value function in finitely many iterations: there is $K$ such that for all $k \ge K$, $\pi_k$ is optimal and $v_{\pi_k} = v_*$.
--
--   This is the correctness of policy iteration, $\pi_0 \to v_{\pi_0} \to \pi_1 \to v_{\pi_1} \to \cdots \to \pi_* \to v_*$.
--
--   **Formalization Note** The statement concerns the idealized sequence with exact policy evaluation. It does not claim that the boxed pseudocode on p. 80 stops: with ties the policy may switch forever between equally good optimal policies (Exercise 4.4, p. 82), which is why the conclusion is "optimal from some $K$ on" rather than "the sequence becomes constant".
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §4.3, p. 80

import Mathlib
import Definitions.Def_SuttonBartoRL_DP_MDP
import Definitions.Def_SuttonBartoRL_DP_ValueFunctions

namespace SuttonBartoRL.DP

/-- Policy iteration, Sutton & Barto (2018), §4.3, p. 80. Let `π_0, π_1, …` be deterministic
policies with each `π_{k+1}` greedy with respect to `q_{π_k}` (ties broken arbitrarily). Then
(1) each policy is a strict improvement over the previous one unless it is already optimal:
either `π_k` is optimal, or `v_{π_{k+1}} ≥ v_{π_k}` everywhere with strict inequality at some state;
and (2) after finitely many iterations the policies are optimal and their values equal `v_*`:
there is `K` with `π_k` optimal and `v_{π_k} = v_*` for all `k ≥ K`. -/
theorem policy_iteration_finite_convergence {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (πs : ℕ → S → A) (hgreedy : ∀ k, IsGreedy M γ (Policy.ofDet (πs k)) (πs (k + 1))) :
    (∀ k, IsOptimalPolicy M γ (Policy.ofDet (πs k)) ∨
      ((∀ s, stateValue M γ (Policy.ofDet (πs k)) s ≤
          stateValue M γ (Policy.ofDet (πs (k + 1))) s) ∧
        ∃ s, stateValue M γ (Policy.ofDet (πs k)) s <
          stateValue M γ (Policy.ofDet (πs (k + 1))) s)) ∧
    (∃ K : ℕ, ∀ k, K ≤ k → IsOptimalPolicy M γ (Policy.ofDet (πs k)) ∧
      ∀ s, stateValue M γ (Policy.ofDet (πs k)) s = optimalValue M γ s) := by sorry

end SuttonBartoRL.DP
