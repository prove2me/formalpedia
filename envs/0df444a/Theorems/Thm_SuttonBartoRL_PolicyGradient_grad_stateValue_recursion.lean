-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_grad_stateValue_recursion
-- name    : SuttonBartoRL.PolicyGradient.grad_stateValue_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:39:36.601511+00:00
-- url     : https://prove2.me/theorems/cefb2311-16b7-480f-a7e7-5eb83c78cc99
-- title:
--   The gradient of $v_\pi$ in terms of $q_\pi$ and $\nabla v_\pi$ (proof box, p. 325)
-- statement:
--   Let a finite episodic MDP and a differentiable policy parameterization be given, and let episodes terminate under $\pi_{\theta_0}$. Then for every nonterminal state $s$ the map $\theta \mapsto v_{\pi_\theta}(s)$ is differentiable at $\theta_0$, and, with $\pi(a\mid s) = \pi(a\mid s,\theta_0)$, $q_\pi = q_{\pi_{\theta_0}}$ and all gradients taken at $\theta_0$,
--   $$
--   \nabla v_\pi(s) = \sum_a \Big[\nabla \pi(a \mid s)\, q_\pi(s,a) + \pi(a\mid s) \sum_{s' \in \mathcal S} p(s' \mid s, a)\, \nabla v_\pi(s')\Big].
--   $$
--
--   This is the recursion that the proof of the policy gradient theorem unrolls.
--
--   **Formalization Note** The existence of $\nabla v_\pi$, used silently in the book, is part of the conclusion. Termination is assumed at $\theta_0$ only; because the policy is continuous in $\theta$, it then holds in a neighbourhood of $\theta_0$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of the Policy Gradient Theorem (episodic case)", first four lines, p. 325

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- Box "Proof of the Policy Gradient Theorem (episodic case)", p. 325, first four lines: if episodes
terminate under `π_{θ₀}`, then every state value `θ ↦ v_{π_θ}(s)` is differentiable at `θ₀` and
`∇v_π(s) = Σ_a [∇π(a|s) q_π(s, a) + π(a|s) Σ_{s'} p(s'|s, a) ∇v_π(s')]`. -/
theorem grad_stateValue_recursion {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) (s : S) :
    HasGradientAt (fun θ => M.stateValue π θ s)
      (∑ a, (M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ +
        π.prob θ₀ s a • ∑ s', M.trans s a s' • gradient (fun θ => M.stateValue π θ s') θ₀))
      θ₀ := by sorry

end SuttonBartoRL.PolicyGradient
