-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_policy_gradient_baseline
-- name    : SuttonBartoRL.PolicyGradient.policy_gradient_baseline
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:38.741981+00:00
-- url     : https://prove2.me/theorems/03d1c6ef-db93-4a9c-bf9d-4d0d2eae8eef
-- title:
--   Policy gradient theorem with baseline (13.10)
-- statement:
--   Let a finite episodic MDP with start state $s_0$ and a differentiable policy parameterization be given, let episodes terminate under $\pi_{\theta_0}$, and let $b : \mathcal S \to \mathbb R$ be any baseline (a function of the state that does not vary with the action). Then:
--
--   1. for every state $s$, $\sum_a b(s)\, \nabla \pi(a \mid s, \theta_0) = 0$;
--   2. $J(\theta) = v_{\pi_\theta}(s_0)$ is differentiable at $\theta_0$ and
--   $$
--   \nabla J(\theta_0) = \Big(\sum_{s'} \eta(s')\Big) \sum_s \mu(s) \sum_a \big(q_\pi(s,a) - b(s)\big)\, \nabla\pi(a\mid s,\theta_0),
--   $$
--   where $\eta$ is the expected number of visits from $s_0$ and $\mu = \eta/\sum\eta$ the on-policy distribution.
--
--   Subtracting a state-dependent baseline leaves the gradient unchanged; this is what REINFORCE with baseline (13.11) relies on.
--
--   **Formalization Note** The book's "∝" is made exact: the constant is $\sum_{s'} \eta(s')$, the average length of an episode (p. 326). The book allows the baseline to be "even a random variable" not depending on the action; here it is a deterministic function of the state.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (13.10) and the display following it, p. 329

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- (13.10), p. 329: the policy gradient theorem with a baseline `b(s)` that does not vary with the
action. For every `b : S → ℝ`, `Σ_a b(s) ∇π(a|s, θ₀) = 0` for every state, and under termination
`∇J(θ₀) = (Σ_{s'} η(s')) Σ_s µ(s) Σ_a (q_π(s, a) − b(s)) ∇π(a|s, θ₀)`. -/
theorem policy_gradient_baseline {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s₀ : S) (θ₀ : EuclideanSpace ℝ (Fin d))
    (b : S → ℝ) (hT : M.Terminates π θ₀) :
    (∀ s, ∑ a, b s • gradient (fun θ => π.prob θ s a) θ₀ = 0) ∧
    HasGradientAt (M.performance π s₀)
      ((∑ s', M.visits π θ₀ s₀ s') • ∑ s, M.onPolicyDist π θ₀ s₀ s •
        ∑ a, (M.actionValue π θ₀ s a - b s) • gradient (fun θ => π.prob θ s a) θ₀) θ₀ := by sorry

end SuttonBartoRL.PolicyGradient
