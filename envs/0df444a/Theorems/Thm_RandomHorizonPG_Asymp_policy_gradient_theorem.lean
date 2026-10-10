-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_policy_gradient_theorem
-- name    : RandomHorizonPG.Asymp.policy_gradient_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:47.240164+00:00
-- url     : https://prove2.me/theorems/bcf66f78-9251-41f6-a5b0-87a17037c8c8
-- title:
--   (3.3)–(3.4), p. 7 — policy gradient theorem: ∇J(θ) = (1/(1−γ)) E_{(s,a)∼ρ_θ}[∇log π_θ(a|s) Q_{π_θ}(s,a)]
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1. Then the objective $J(\theta)=V_{\pi_\theta}(s_0)$ is differentiable at every $\theta\in\mathbb R^d$, with gradient
--   $$
--   \nabla J(\theta)=\frac1{1-\gamma}\sum_{s\in\mathcal S}\sum_{a\in\mathcal A}\rho_{\pi_\theta}(s)\,\pi_\theta(a\mid s)\,Q_{\pi_\theta}(s,a)\,\nabla\log\pi_\theta(a\mid s)=\frac1{1-\gamma}\,\mathbb E_{(s,a)\sim\rho_\theta}\big[\nabla\log\pi_\theta(a\mid s)\,Q_{\pi_\theta}(s,a)\big],
--   $$
--   where $\rho_{\pi_\theta}(s)=(1-\gamma)\sum_{t\ge0}\gamma^tp(s_t=s\mid s_0,\pi_\theta)$ is the discounted state-occupancy measure.
--
--   This is the policy gradient theorem in the form (3.4) used by the paper: it is what the RPG estimator samples without bias, and it is the starting point of the smoothness bound (Lemma 3.2).
--
--   **Formalization Note** The conclusion is `HasGradientAt`, which asserts differentiability as well as the value of the gradient; differentiability of $J$ is not assumed. Finite state and action spaces, where the paper's $\int$ is a sum (footnote 3).
-- source:
--   arXiv:1906.08383v3, (3.3)–(3.4), p. 7

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning

/-- arXiv:1906.08383v3, (3.3)–(3.4), p. 7 (policy gradient theorem): under Assumption 3.1, `J` is
differentiable and
`∇J(θ) = (1/(1−γ)) Σ_{s,a} ρ_{π_θ}(s) π_θ(a|s) Q_{π_θ}(s,a) ∇ log π_θ(a|s)`. -/
theorem policy_gradient_theorem {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ) :
    ∀ θ : EuclideanSpace ℝ (Fin d), HasGradientAt (objective P R γ π s₀)
      ((1 / (1 - γ)) • ∑ s : S, ∑ a : A,
        (occupancy P γ π s₀ θ s * π θ s a * QFunction (π θ) P R γ s a) • score π θ s a) θ := by sorry

end RandomHorizonPG.Asymp
