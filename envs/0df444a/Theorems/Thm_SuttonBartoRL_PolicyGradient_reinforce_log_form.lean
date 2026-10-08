-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_reinforce_log_form
-- name    : SuttonBartoRL.PolicyGradient.reinforce_log_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:39:52.075827+00:00
-- url     : https://prove2.me/theorems/e92c0017-af93-4df1-8138-238997afeddf
-- title:
--   Multiplying and dividing by $\pi(a\mid s,\theta)$ — the log form of the REINFORCE derivation
-- statement:
--   Let a finite episodic MDP with fixed start state $s_0$ and no discounting ($\gamma = 1$) be given, with a differentiable policy parameterization $\pi(a \mid s, \theta)$, $\theta \in \mathbb R^{d'}$. Fix $\theta_0$ such that episodes terminate under $\pi_{\theta_0}$ and every action has positive probability in every state, $\pi(a \mid s, \theta_0) > 0$. Write $q_\pi = q_{\pi_{\theta_0}}$, $\eta$ for the expected number of visits from $s_0$, $\mu = \eta / \sum_{s'} \eta(s')$ for the on-policy distribution and $J(\theta) = v_{\pi_\theta}(s_0)$; all gradients are at $\theta_0$. Then
--
--   1. in every state $s$, multiplying and dividing the summed terms by $\pi(a \mid s, \theta_0)$ leaves the sum unchanged:
--   $$
--   \sum_a q_\pi(s,a)\, \nabla \pi(a \mid s, \theta_0) = \sum_a \pi(a\mid s,\theta_0)\, q_\pi(s,a)\, \nabla \ln \pi(a \mid s, \theta_0);
--   $$
--   2. $J$ is differentiable at $\theta_0$ and
--   $$
--   \nabla J(\theta_0) = \Big(\sum_{s'} \eta(s')\Big) \sum_s \mu(s) \sum_a \pi(a\mid s,\theta_0)\, q_\pi(s,a)\, \nabla \ln \pi(a \mid s, \theta_0).
--   $$
--
--   The right-hand side of 2 is the book's $\nabla J(\theta) \propto \mathbb E_\pi\big[\sum_a \pi(a\mid S_t,\theta) q_\pi(S_t,a) \nabla\pi(a\mid S_t,\theta)/\pi(a\mid S_t,\theta)\big] = \mathbb E_\pi\big[q_\pi(S_t,A_t) \nabla\pi(A_t\mid S_t,\theta)/\pi(A_t\mid S_t,\theta)\big]$ written out, with $S_t$ distributed as $\mu$ and $A_t \sim \pi(\cdot \mid S_t, \theta_0)$, the constant of proportionality made explicit, and $\nabla\pi/\pi$ written as $\nabla \ln \pi$ (the identity $\nabla \ln x = \nabla x / x$, p. 327). It is the step from the policy gradient theorem to the REINFORCE update (13.8).
--
--   **Formalization Note** Termination under $\pi_{\theta_0}$ ($\sum_k P_{\theta_0}^k$ finite entrywise) is the implicit standing assumption of the episodic case. The positivity hypothesis is the book's "the policy never becomes deterministic" (p. 322), needed for $\ln \pi$ to be differentiable. The book's last line, $\mathbb E_\pi[G_t \nabla\pi(A_t\mid S_t,\theta)/\pi(A_t\mid S_t,\theta)]$, needs a probability space of trajectories and is not stated.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §13.3, derivation of REINFORCE, p. 327, and the identity ∇ ln x = ∇x/x, p. 327

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- §13.3, p. 327 (the derivation of REINFORCE, with the identity `∇ ln x = ∇x / x`): if episodes
terminate under `π_{θ₀}` and every action has positive probability in every state under `π_{θ₀}`, then
1. in every state `s`, `Σ_a q_π(s, a) ∇π(a|s, θ₀) = Σ_a π(a|s, θ₀) q_π(s, a) ∇ ln π(a|s, θ₀)`
   (multiplying and dividing the summed terms by `π(a|s, θ₀)` does not change the equality);
2. `J` is differentiable at `θ₀` and
   `∇J(θ₀) = (Σ_{s'} η(s')) Σ_s µ(s) Σ_a π(a|s, θ₀) q_π(s, a) ∇ ln π(a|s, θ₀)`, the exact form of
   `∇J(θ) ∝ E_π[Σ_a π(a|S_t, θ) q_π(S_t, a) ∇π(a|S_t, θ)/π(a|S_t, θ)] = E_π[q_π(S_t, A_t) ∇π(A_t|S_t, θ)/π(A_t|S_t, θ)]`
   with `S_t ∼ µ` and `A_t ∼ π(·|S_t, θ₀)`. -/
theorem reinforce_log_form {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s₀ : S) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) (hpos : ∀ s a, 0 < π.prob θ₀ s a) :
    (∀ s, ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ =
      ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
        gradient (fun θ => Real.log (π.prob θ s a)) θ₀) ∧
    HasGradientAt (M.performance π s₀)
      ((∑ s', M.visits π θ₀ s₀ s') • ∑ s, M.onPolicyDist π θ₀ s₀ s •
        ∑ a, (π.prob θ₀ s a * M.actionValue π θ₀ s a) •
          gradient (fun θ => Real.log (π.prob θ s a)) θ₀) θ₀ := by sorry

end SuttonBartoRL.PolicyGradient
