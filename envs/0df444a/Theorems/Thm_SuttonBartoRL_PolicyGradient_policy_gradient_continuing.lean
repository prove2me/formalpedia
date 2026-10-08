-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_policy_gradient_continuing
-- name    : SuttonBartoRL.PolicyGradient.policy_gradient_continuing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:32.589807+00:00
-- url     : https://prove2.me/theorems/f5eaa3f5-c169-437e-94e9-075aeb7b235d
-- title:
--   The policy gradient theorem, continuing case
-- statement:
--   Let a finite continuing MDP and a differentiable policy parameterization be given, fix an initial state $s_0$ and a parameter $\theta_0$ at which the chain is ergodic: $\mu(s') = \lim_{t\to\infty} \Pr\{S_t = s' \mid S_0 = s\}$ exists and does not depend on $s$. Let $J(\theta) = r(\pi_\theta)$ be the average reward (13.15) and $q_\pi$ the differential action value (13.17) of $\pi = \pi_{\theta_0}$. Then $J$ is differentiable at $\theta_0$ and
--   $$
--   \nabla J(\theta_0) = \sum_s \mu(s) \sum_a \nabla \pi(a\mid s, \theta_0)\, q_\pi(s,a).
--   $$
--
--   In the continuing case the constant of proportionality of (13.5) is $1$; the result is the basis of the continuing actor–critic algorithm.
--
--   **Formalization Note** Only ergodicity at $\theta_0$ is assumed, in the book's words. The book's proof also uses that the differential values $v_\pi(s)$ are differentiable in $\theta$; under ergodicity and differentiability of the policy this is a consequence, not an assumption, so it is not a hypothesis here.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §13.6, pp. 333–334, and box "Proof of the Policy Gradient Theorem (continuing case)", pp. 334–335

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_ContinuingValues

namespace SuttonBartoRL.PolicyGradient

/-- The policy gradient theorem, continuing case: §13.6, p. 334, and the box "Proof of the Policy
Gradient Theorem (continuing case)", pp. 334–335. For a finite continuing MDP and a differentiable
policy parameterization that is ergodic at `θ₀` (the steady-state distribution `µ` exists and does
not depend on `S_0`, (13.15)), the average reward `J(θ) = r(π)` (13.15) is differentiable at `θ₀` and
`∇J(θ₀) = Σ_s µ(s) Σ_a q_π(s, a) ∇π(a|s, θ₀)`, with `q_π` the differential action value (13.17). -/
theorem policy_gradient_continuing {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : ContinuingMDP S A) (π : ParamPolicy S A d) (s₀ : S) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hErg : M.IsErgodic π θ₀) :
    HasGradientAt (M.avgReward π s₀)
      (∑ s, M.steadyState π θ₀ s₀ s •
        ∑ a, M.diffActionValue π s₀ θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀) θ₀ := by sorry

end SuttonBartoRL.PolicyGradient
