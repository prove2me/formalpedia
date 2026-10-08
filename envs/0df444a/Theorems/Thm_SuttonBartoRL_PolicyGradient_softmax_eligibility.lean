-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_softmax_eligibility
-- name    : SuttonBartoRL.PolicyGradient.softmax_eligibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:16:24.685157+00:00
-- url     : https://prove2.me/theorems/49c0b3df-567f-439a-869a-7d491169e8df
-- title:
--   Exercise 13.3 — eligibility vector of the linear soft-max policy (13.9)
-- statement:
--   Let $\mathcal A$ be a finite nonempty action set, $x(s,a) \in \mathbb R^{d'}$ feature vectors, and $\pi(a\mid s,\theta) = e^{\theta^\top x(s,a)} / \sum_b e^{\theta^\top x(s,b)}$ the soft-max in linear action preferences. Then for every $s$, $a$ and $\theta$ the map $\theta \mapsto \ln \pi(a \mid s,\theta)$ is differentiable and
--   $$
--   \nabla \ln \pi(a \mid s, \theta) = x(s,a) - \sum_b \pi(b \mid s, \theta)\, x(s,b).
--   $$
--
--   This eligibility vector is what REINFORCE and actor–critic methods compute at every step for the linear soft-max parameterization.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 13.3, Eq. (13.9), p. 329

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_SoftmaxPolicy

namespace SuttonBartoRL.PolicyGradient

/-- Exercise 13.3 and (13.9), p. 329: for the soft-max in action preferences (13.2) with linear
preferences `h(s, a, θ) = θᵀ x(s, a)` (13.3), the eligibility vector is
`∇ ln π(a|s, θ) = x(s, a) − Σ_b π(b|s, θ) x(s, b)`, for every `s`, `a`, `θ`. -/
theorem softmax_eligibility {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (x : S → A → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) (s : S) (a : A) :
    HasGradientAt (fun θ' => Real.log (softmaxPolicy (linearPref x) θ' s a))
      (x s a - ∑ b, softmaxPolicy (linearPref x) θ s b • x s b) θ := by sorry

end SuttonBartoRL.PolicyGradient
