-- Prove2me | Theorems.Thm_SampleComplexityRL_PolicyGrad_tepoch_policy_gradient
-- name    : SampleComplexityRL.PolicyGrad.tepoch_policy_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:18.045361+00:00
-- url     : https://prove2.me/theorems/6077a6e3-8f91-4ea0-9adb-97165d4e4c3d
-- title:
--   Theorem 4.2.3 — T-epoch policy gradient: ∇V_π(s₀) = T·E_{(s,t)∼d_{π,s₀}}[Σ_a ∇π(a|s,t,θ) Q_{π,t}(s,a)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function, $T\ge1$ a horizon and $s_0\in S$ a start state. Let $\pi(a\mid s,t,\theta)$, $\theta\in\mathbb R^k$, be a parameterized non-stationary policy: for every $\theta$, $\pi(\cdot\mid s,t,\theta)$ is a probability distribution on $A$ for every state $s$ and epoch $t<T$. Fix $\theta_0\in\mathbb R^k$ and assume that every map $\theta\mapsto\pi(a\mid s,t,\theta)$ ($t<T$) is differentiable at $\theta_0$, with gradient $\nabla\pi(a\mid s,t,\theta_0)$.
--
--   Then the normalized $T$-epoch value $\theta\mapsto V_{\pi_\theta}(s_0)$ is differentiable at $\theta_0$, and its gradient is
--   $$
--   \nabla V_\pi(s_0)=T\,\mathbb E_{(s,t)\sim d_{\pi,s_0}}\Big[\sum_a\nabla\pi(a\mid s,t,\theta_0)\,Q_{\pi,t}(s,a)\Big]
--   =T\sum_{s\in S}\sum_{t=0}^{T-1}d_{\pi,s_0}(s,t)\sum_{a\in A}Q_{\pi,t}(s,a)\,\nabla\pi(a\mid s,t,\theta_0),
--   $$
--   where $\pi=\pi_{\theta_0}$, $d_{\pi,s_0}(s,t)=\frac1T\Pr(s_t=s\mid\pi,s_0)$ is the future state-time distribution, and $Q_{\pi,t}(s,a)=\frac1T r(s,a)+\mathbb E_{s'\sim P(\cdot\mid s,a)}[V_{\pi,t+1}(s')]$ is the normalized $t$ state-action value.
--
--   The gradient is an expectation over state-times but a sum over actions, which is what makes it amenable to sampling from $d_{\pi,s_0}$; this form is the basis of the estimation analysis of §4.2.3.
--
--   **Formalization Note** The parameter space is `EuclideanSpace ℝ (Fin k)`. The derivative is stated with `HasFDerivAt`, so differentiability of the value is part of the conclusion; the derivative of each policy entry is `fderiv` of a map assumed differentiable at $\theta_0$, i.e. the Fréchet derivative (a linear functional, the gradient's inner-product form). Epochs are 0-based; the factor $T$ compensates the $1/T$ carried by both $d_{\pi,s_0}$ and $Q_{\pi,t}$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 48, Theorem 4.2.3 (with the standing assumptions of §4.2.2, p. 48)

import Mathlib
import Definitions.Def_SampleComplexityRL_PolicyGrad_TEpoch

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning

/-- Kakade 2003, Theorem 4.2.3 (p. 48): for a non-stationary parameterized policy
`π(a|s,t,θ)`, `θ ∈ ℝ^k`, whose entries at the epochs `t < T` are differentiable at `θ₀`, the
normalized `T`-epoch value `θ ↦ V_{π_θ}(s₀)` is differentiable at `θ₀` with
`∇V_π(s₀) = T E_{(s,t) ∼ d_{π,s₀}}[Σ_a ∇π(a|s,t,θ) Q_{π,t}(s,a)]`. -/
theorem tepoch_policy_gradient {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] {k : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (π : EuclideanSpace ℝ (Fin k) → NSPolicy S A) (θ₀ : EuclideanSpace ℝ (Fin k)) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hT : 0 < T)
    (hπ : ∀ θ, IsNSPolicy T (π θ))
    (hdiff : ∀ t < T, ∀ s a, DifferentiableAt ℝ (fun θ => π θ t s a) θ₀) :
    HasFDerivAt (fun θ => value P r T (π θ) s₀)
      ((T : ℝ) •
        ∑ s, ∑ t ∈ Finset.range T, stateTimeDist P (π θ₀) s₀ T s t •
          ∑ a, tQValue P r T (π θ₀) t s a • fderiv ℝ (fun θ => π θ t s a) θ₀)
      θ₀ := by sorry

end SampleComplexityRL.PolicyGrad
