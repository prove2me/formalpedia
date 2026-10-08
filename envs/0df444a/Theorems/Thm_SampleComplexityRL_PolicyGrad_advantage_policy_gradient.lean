-- Prove2me | Theorems.Thm_SampleComplexityRL_PolicyGrad_advantage_policy_gradient
-- name    : SampleComplexityRL.PolicyGrad.advantage_policy_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:11:59.161451+00:00
-- url     : https://prove2.me/theorems/a3032911-98bc-4c7a-b88f-558999b97697
-- title:
--   §5.4.2, p. 66 — advantage form of the discounted policy gradient: ∇V_π(s₀) = A/(1−γ)·E_{s∼d_{π,s₀}}E_{a∼Uniform}[A_π(s,a)∇π(a|s,θ)]
-- statement:
--   Let $S$ be a finite state set, $A$ a finite nonempty action set with $|A|$ elements, $P(s'\mid s,a)$ a transition kernel, $r:S\times A\to[0,1]$ a reward function, $0\le\gamma<1$ a discount factor and $s_0\in S$. Let $\pi(a\mid s,\theta)$, $\theta\in\mathbb R^k$, be a stationary parameterized policy (a probability distribution on $A$ for every $s$ and $\theta$), and assume every map $\theta\mapsto\pi(a\mid s,\theta)$ is differentiable at $\theta_0$.
--
--   Then $\theta\mapsto V_{\pi_\theta,\gamma}(s_0)$ is differentiable at $\theta_0$ and, with $\pi=\pi_{\theta_0}$,
--   $$
--   \nabla V_\pi(s_0)=\frac{|A|}{1-\gamma}\,\mathbb E_{s\sim d_{\pi,s_0}}\,\mathbb E_{a\sim\mathrm{Uniform}}\big[A_\pi(s,a)\,\nabla\pi(a\mid s,\theta_0)\big]
--   =\frac{|A|}{1-\gamma}\sum_{s}d_{\pi,s_0}(s)\,\frac1{|A|}\sum_a A_\pi(s,a)\,\nabla\pi(a\mid s,\theta_0),
--   $$
--   where $d_{\pi,s_0}=d_{\pi,s_0,\gamma}$ is the $\gamma$-discounted future state distribution and $A_\pi(s,a)=Q_{\pi,\gamma}(s,a)-V_{\pi,\gamma}(s)$ is the normalized advantage.
--
--   This form shows that the gradient is governed by the advantages under the *current* policy's state distribution $d_{\pi,s_0}$, which the thesis contrasts with the distribution $d_{\pi^*,s_0}$ that matters for near-optimality (the "mismeasure" of gradient methods).
--
--   **Formalization Note** $|A|$ is `Fintype.card A` (positive since $A$ is nonempty), and the uniform expectation is written as $\frac1{|A|}\sum_a$, as on the page. Values, advantages and $d_{\pi,s_0,\gamma}$ come from the published normalized model `ApproxOptRL.Shared.Model`. The derivative is stated with `HasFDerivAt`.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, pp. 65–66, Section 5.4.2, last line of the display on p. 66

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_ApproxOptRL_Shared_Model

namespace SampleComplexityRL.PolicyGrad

open FoundationsML.ReinforcementLearning ApproxOptRL.Shared

/-- Kakade 2003, §5.4.2 (pp. 65–66, last line of the display): the advantage form of the
discounted policy gradient,
`∇V_π(s₀) = (A/(1-γ)) E_{s ∼ d_{π,s₀}} E_{a ∼ Uniform}[A_π(s,a) ∇π(a|s,θ)]`,
with `A = |A|` the number of actions and `E_{a ∼ Uniform}[f] = (1/A) Σ_a f(a)`. -/
theorem advantage_policy_gradient {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] {k : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (π : EuclideanSpace ℝ (Fin k) → S → A → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (s₀ : S)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hπ : ∀ θ, IsPolicy (π θ))
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ => π θ s a) θ₀) :
    HasFDerivAt (fun θ => ApproxOptRL.Shared.value P r γ (π θ) s₀)
      (((Fintype.card A : ℝ) / (1 - γ)) •
        ∑ s, futureStateDist P γ (π θ₀) (fun s' => if s' = s₀ then 1 else 0) s •
          ((1 / (Fintype.card A : ℝ)) •
            ∑ a, advantage P r γ (π θ₀) s a • fderiv ℝ (fun θ => π θ s a) θ₀))
      θ₀ := by sorry

end SampleComplexityRL.PolicyGrad
