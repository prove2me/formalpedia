-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_lipschitz_policy_gradient
-- name    : RandomHorizonPG.Asymp.lipschitz_policy_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:50.176328+00:00
-- url     : https://prove2.me/theorems/60bc45c2-683a-4c12-b2f0-c26aa4ac2700
-- title:
--   Lemma 3.2, p. 8 — under Assumption 3.1, ∇J is L-Lipschitz with L = U_R L_Θ/(1−γ)² + (1+γ)U_R B_Θ²/(1−γ)³
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1 with constants $U_R,L_\Theta,B_\Theta$. Then for all $\theta^1,\theta^2\in\mathbb R^d$,
--   $$
--   \|\nabla J(\theta^1)-\nabla J(\theta^2)\|\le L\,\|\theta^1-\theta^2\|,\qquad L:=\frac{U_R\,L_\Theta}{(1-\gamma)^2}+\frac{(1+\gamma)\,U_R\,B_\Theta^2}{(1-\gamma)^3}. \qquad (3.6)
--   $$
--
--   The smoothness constant $L$ enters the ascent inequality of Lemma A.1, the definition of the auxiliary process $W_k$, and the rate of Corollary 4.4.
--
--   **Formalization Note** The page's "with some constant $L>0$" is not stated separately: $L>0$ would require $U_R>0$, which the page does not assume, and the explicit value (3.6) is what the later results use. Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, Lemma 3.2 and (3.6), p. 8

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning

/-- arXiv:1906.08383v3, Lemma 3.2, p. 8: under Assumption 3.1, `∇J` is Lipschitz with the constant
`L = U_R L_Θ/(1−γ)² + (1+γ) U_R B_Θ²/(1−γ)³` of (3.6). -/
theorem lipschitz_policy_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ) :
    ∀ θ₁ θ₂ : EuclideanSpace ℝ (Fin d),
      ‖gradient (objective P R γ π s₀) θ₁ - gradient (objective P R γ π s₀) θ₂‖ ≤
        (UR * LΘ / (1 - γ) ^ 2 + (1 + γ) * UR * BΘ ^ 2 / (1 - γ) ^ 3) * ‖θ₁ - θ₂‖ := by sorry

end RandomHorizonPG.Asymp
