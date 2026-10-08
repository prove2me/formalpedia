-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_futility_of_discounting
-- name    : SuttonBartoRL.AverageReward.futility_of_discounting
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:01:55.216313+00:00
-- url     : https://prove2.me/theorems/3f59269c-189f-4f41-a8be-abec78c6f7f2
-- title:
--   The futility of discounting: $J(\pi) = \sum_s \mu_\pi(s) v^\gamma_\pi(s) = r(\pi)/(1-\gamma)$
-- statement:
--   Fix a finite MDP with dynamics $p(s', r\mid s, a)$ and a discount rate $0 \le \gamma < 1$. For a policy $\pi$ let $\mu_\pi$ be a stationary distribution of $\pi$, i.e. a probability vector with $\sum_s \mu_\pi(s)\sum_a\pi(a\mid s)\,p(s'\mid s,a) = \mu_\pi(s')$ (10.8); let
--   $$
--   r(\pi) = \sum_s \mu_\pi(s)\sum_a \pi(a\mid s)\sum_{s', r} p(s', r\mid s, a)\, r
--   $$
--   be the average reward (10.7), and $v^\gamma_\pi$ the discounted value function. Then the discounted objective satisfies
--   $$
--   J(\pi) = \sum_s \mu_\pi(s)\, v^\gamma_\pi(s) = \frac{1}{1-\gamma}\, r(\pi).
--   $$
--   Consequently, for a fixed $\gamma$ and any two policies $\pi, \pi'$ with stationary distributions $\mu_\pi, \mu_{\pi'}$,
--   $$
--   J(\pi) \le J(\pi') \iff r(\pi) \le r(\pi') .
--   $$
--
--   Averaging discounted values over the on-policy distribution orders policies exactly as the undiscounted average reward does; the discount rate has no influence on the ordering. This is the book's argument that discounting has no role in the definition of the control problem with function approximation.
--
--   **Formalization Note** The identity is stated for every stationary distribution $\mu$ of $\pi$, which is all the book's derivation uses; no ergodicity is assumed (under ergodicity $\mu_\pi$ is the unique stationary distribution, and the average reward is the long-run rate (10.6) by the milestone on (10.6)–(10.7)). The value $v^\gamma_\pi$ is the expected discounted return, defined as a series, not as a solution of the Bellman equation. $\gamma = 0$ is allowed, as on p. 253.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "The Futility of Discounting in Continuing Problems", p. 254; §10.4, p. 253

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), box "The Futility of Discounting in Continuing Problems", p. 254, and
§10.4, p. 253. Fix a finite MDP and a discount rate `0 ≤ γ < 1`. For every policy `π` and every
stationary distribution `μ` of `π` ((10.8)), the discounted objective
`J(π) = Σ_s μ(s) v^γ_π(s)` equals `r(π) / (1 − γ)`, where
`r(π) = Σ_s μ(s) Σ_a π(a | s) Σ_{s', r} p(s', r | s, a) r` ((10.7)). Consequently, for a fixed `γ`,
`J` orders policies (each with its own stationary distribution) exactly as the average reward does. -/
theorem futility_of_discounting {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∀ (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ), IsStationaryDist M π μ →
      discountedObjective M γ π μ = (1 / (1 - γ)) * avgReward M π μ) ∧
    (∀ (π π' : SuttonBartoRL.FiniteMDP.Policy S A) (μ μ' : S → ℝ), IsStationaryDist M π μ → IsStationaryDist M π' μ' →
      (discountedObjective M γ π μ ≤ discountedObjective M γ π' μ' ↔
        avgReward M π μ ≤ avgReward M π' μ')) := by sorry

end SuttonBartoRL.AverageReward
