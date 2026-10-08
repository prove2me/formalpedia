-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_bellman_operator_unique_fixed_point
-- name    : SuttonBartoRL.OffPolicy.bellman_operator_unique_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:01:44.299432+00:00
-- url     : https://prove2.me/theorems/33971534-1f39-4654-a7dd-98ca1d6b6abc
-- title:
--   (11.21) — v_π is the only fixed point of the Bellman operator
-- statement:
--   Let a finite MDP, a policy $\pi$ and a discount $0\le\gamma<1$ be given, and let $v_\pi(s) = \mathbb E_\pi\bigl[\sum_{k\ge0}\gamma^k R_{t+k+1}\mid S_t = s\bigr]$ be the true value function. Then $v_\pi$ is a fixed point of the Bellman operator $B_\pi$ of (11.20), and the only one:
--   $$
--   v_\pi = B_\pi v_\pi, \qquad B_\pi v = v \implies v = v_\pi .
--   $$
--
--   This is the Bellman equation (11.16) written as a fixed-point statement; it is what makes $\bar\delta_{\mathbf w} = B_\pi v_{\mathbf w} - v_{\mathbf w}$ a measure of how far $v_{\mathbf w}$ is from $v_\pi$.
--
--   **Formalization Note** $v_\pi$ is defined from expected returns as $\sum_k\gamma^k P_\pi^k r_\pi$, not as a solution of the Bellman equation. Only the discounted case $\gamma<1$ is stated; the book's episodic case $\gamma = 1$ with termination is not.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, (11.16) p. 267; (11.20)–(11.21), p. 269

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), (11.21), p. 269: for a finite MDP, a policy `π` and `0 ≤ γ < 1`, the true
value function `v_π` (defined from expected discounted returns, (3.12)) is a fixed point of the
Bellman operator `B_π` (11.20), and it is the only one: `v_π = B_π v_π`, and `B_π v = v` implies
`v = v_π`. -/
theorem bellman_operator_unique_fixed_point {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    bellmanOp M π γ (stateValue M γ π) = stateValue M γ π ∧
    ∀ v : S → ℝ, bellmanOp M π γ v = v → v = stateValue M γ π := by sorry

end SuttonBartoRL.OffPolicy
