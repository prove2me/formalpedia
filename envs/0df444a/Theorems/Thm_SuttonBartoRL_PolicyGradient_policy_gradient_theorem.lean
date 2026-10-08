-- Prove2me | Theorems.Thm_SuttonBartoRL_PolicyGradient_policy_gradient_theorem
-- name    : SuttonBartoRL.PolicyGradient.policy_gradient_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:58.543139+00:00
-- url     : https://prove2.me/theorems/716a913a-8453-4d32-bf0a-1230cd4a0999
-- title:
--   The policy gradient theorem, episodic case (13.5)
-- statement:
--   Let a finite episodic MDP with a fixed start state $s_0$ be given, with no discounting ($\gamma = 1$), and let $\pi(a \mid s, \theta)$, $\theta \in \mathbb R^{d'}$, be a differentiable policy parameterization. Let $J(\theta) = v_{\pi_\theta}(s_0)$ (13.4). Fix $\theta_0$ such that episodes terminate under $\pi = \pi_{\theta_0}$, let $q_\pi$ be its action values, $\eta(s) = \sum_{k\ge0}\Pr(s_0 \to s, k, \pi)$ the expected number of visits to $s$ in an episode, and $\mu(s) = \eta(s)/\sum_{s'}\eta(s')$ the on-policy distribution (9.3). Then:
--
--   1. $J$ is differentiable at $\theta_0$, and
--   $$
--   \nabla J(\theta_0) = \sum_s \eta(s) \sum_a q_\pi(s,a)\, \nabla \pi(a \mid s, \theta_0);
--   $$
--   2. this equals
--   $$
--   \Big(\sum_{s'} \eta(s')\Big) \sum_s \mu(s) \sum_a q_\pi(s,a)\, \nabla \pi(a \mid s, \theta_0);
--   $$
--   3. the constant $\sum_{s'} \eta(s')$, the average length of an episode, is at least $1$.
--
--   Together these are the book's $\nabla J(\theta) \propto \sum_s \mu(s) \sum_a q_\pi(s,a) \nabla\pi(a\mid s,\theta)$ with its constant of proportionality made explicit. The gradient of performance involves no derivative of the state distribution, which is what makes sample-based gradient ascent (REINFORCE, actor–critic) possible.
--
--   **Formalization Note** The book writes "∝"; the statement gives the exact equality of the second-to-last line of the proof box, with the constant named on p. 326. Termination at $\theta_0$ is the book's implicit assumption for $\gamma = 1$, stated as a hypothesis: the expected number of visits to every nonterminal state from every nonterminal state is finite. Gradients are vectors in $\mathbb R^{d'}$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, policy gradient theorem (13.5), p. 326, with the box "Proof of the Policy Gradient Theorem (episodic case)", p. 325, (13.4), p. 324, and (9.3), p. 199

import Mathlib
import Definitions.Def_SuttonBartoRL_PolicyGradient_Model
import Definitions.Def_SuttonBartoRL_PolicyGradient_EpisodicValues

namespace SuttonBartoRL.PolicyGradient

/-- **The policy gradient theorem, episodic case** (13.5), p. 326, with its proof box, p. 325. For a
finite episodic MDP with fixed start state `s₀`, `γ = 1`, `J(θ) = v_{π_θ}(s₀)` (13.4), and a
differentiable policy parameterization under which episodes terminate at `θ₀`:
1. `J` is differentiable at `θ₀` and `∇J(θ₀) = Σ_s η(s) Σ_a q_π(s, a) ∇π(a|s, θ₀)`;
2. this equals `(Σ_{s'} η(s')) Σ_s µ(s) Σ_a q_π(s, a) ∇π(a|s, θ₀)` with `µ = η / Σ η` (9.3);
3. the constant of proportionality `Σ_{s'} η(s')`, the average length of an episode, is at least `1`. -/
theorem policy_gradient_theorem {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : EpisodicMDP S A) (π : ParamPolicy S A d) (s₀ : S) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hT : M.Terminates π θ₀) :
    HasGradientAt (M.performance π s₀)
      (∑ s, M.visits π θ₀ s₀ s •
        ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀) θ₀ ∧
    (∑ s, M.visits π θ₀ s₀ s •
        ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀) =
      (∑ s', M.visits π θ₀ s₀ s') • ∑ s, M.onPolicyDist π θ₀ s₀ s •
        ∑ a, M.actionValue π θ₀ s a • gradient (fun θ => π.prob θ s a) θ₀ ∧
    1 ≤ ∑ s', M.visits π θ₀ s₀ s' := by sorry

end SuttonBartoRL.PolicyGradient
