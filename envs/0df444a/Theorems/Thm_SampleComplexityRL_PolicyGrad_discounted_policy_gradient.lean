-- Prove2me | Theorems.Thm_SampleComplexityRL_PolicyGrad_discounted_policy_gradient
-- name    : SampleComplexityRL.PolicyGrad.discounted_policy_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:03.618927+00:00
-- url     : https://prove2.me/theorems/a380c3cf-09cf-4127-8df9-91aab1f1d19e
-- title:
--   Theorem 4.2.4 — discounted policy gradient: ∇V_{π,γ}(s₀) = (1/(1−γ))·E_{s∼d_{π,s₀,γ}}[Σ_a ∇π(a|s,θ) Q_{π,γ}(s,a)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function, $0\le\gamma<1$ a discount factor and $s_0\in S$ a start state. Let $\pi(a\mid s,\theta)$, $\theta\in\mathbb R^k$, be a stationary parameterized policy: $\pi(\cdot\mid s,\theta)$ is a probability distribution on $A$ for every state $s$ and every $\theta$. Fix $\theta_0$ and assume every map $\theta\mapsto\pi(a\mid s,\theta)$ is differentiable at $\theta_0$, with gradient $\nabla\pi(a\mid s,\theta_0)$.
--
--   Then the normalized discounted value $\theta\mapsto V_{\pi_\theta,\gamma}(s_0)$ is differentiable at $\theta_0$, and with $\pi=\pi_{\theta_0}$
--   $$
--   \nabla V_{\pi,\gamma}(s_0)=\frac1{1-\gamma}\,\mathbb E_{s\sim d_{\pi,s_0,\gamma}}\Big[\sum_a\nabla\pi(a\mid s,\theta_0)\,Q_{\pi,\gamma}(s,a)\Big]
--   =\frac1{1-\gamma}\sum_{s\in S}d_{\pi,s_0,\gamma}(s)\sum_{a\in A}Q_{\pi,\gamma}(s,a)\,\nabla\pi(a\mid s,\theta_0).
--   $$
--   Here $V_{\pi,\gamma}(s)=(1-\gamma)\mathbb E[\sum_{\tau\ge0}\gamma^\tau r(s_\tau,a_\tau)\mid\pi,s_0=s]$ is the normalized value, $Q_{\pi,\gamma}(s,a)=(1-\gamma)r(s,a)+\gamma\,\mathbb E_{s'\sim P(\cdot\mid s,a)}[V_{\pi,\gamma}(s')]$ the normalized state-action value, and $d_{\pi,s_0,\gamma}(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr(s_t=s\mid\pi,s_0)$ the $\gamma$-discounted future state distribution.
--
--   This is the policy gradient theorem of Sutton, McAllester, Singh and Mansour in the thesis's normalized convention. It expresses the gradient of the performance through quantities of the current policy only, and is the starting point of the thesis's analysis of gradient methods.
--
--   **Formalization Note** The parameter space is `EuclideanSpace ℝ (Fin k)`. The derivative is stated with `HasFDerivAt`, so differentiability of the value map is part of the conclusion rather than an assumption; $\nabla\pi$ is the Fréchet derivative (`fderiv`) of a map assumed differentiable at $\theta_0$. Value, $Q$ and $d_{\pi,s_0,\gamma}$ are from the published normalized model `ApproxOptRL.Shared.Model`, with $d_{\pi,s_0,\gamma}$ its `futureStateDist` at the point mass on $s_0$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 48, Theorem 4.2.4 (with the standing assumptions of §4.2.2, p. 48)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared

/-- Kakade 2003, Theorem 4.2.4 (p. 48): for a stationary parameterized policy `π(a|s,θ)`,
`θ ∈ ℝ^k`, whose entries are differentiable at `θ₀`, the normalized discounted value
`θ ↦ V_{π_θ,γ}(s₀)` is differentiable at `θ₀` with
`∇V_{π,γ}(s₀) = (1/(1-γ)) E_{s ∼ d_{π,s₀,γ}}[Σ_a ∇π(a|s,θ) Q_{π,γ}(s,a)]`. -/
theorem discounted_policy_gradient {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] {k : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π : EuclideanSpace ℝ (Fin k) → S → A → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hπ : ∀ θ, IsPolicy (π θ))
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ => π θ s a) θ₀) :
    HasFDerivAt (fun θ => ApproxOptRL.Shared.value P r γ (π θ) s₀)
      ((1 / (1 - γ)) •
        ∑ s, futureStateDist P γ (π θ₀) (fun s' => if s' = s₀ then 1 else 0) s •
          ∑ a, qValue P r γ (π θ₀) s a • fderiv ℝ (fun θ => π θ s a) θ₀)
      θ₀ := by sorry

end SampleComplexityRL.PolicyGrad
