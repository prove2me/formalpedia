-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_weighted_gradient_summable
-- name    : RandomHorizonPG.Asymp.weighted_gradient_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:38.183988+00:00
-- url     : https://prove2.me/theorems/3a842496-06dc-41f7-9a26-01064025607c
-- title:
--   (A.26), p. 28 — along an RPG run with Σα_k² < ∞, Σ_k α_k‖∇J(θ_k)‖² < ∞ almost surely
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1. Let $(\theta_k)$ be a run of Algorithm 3 (RPG) with positive stepsizes satisfying $\sum_k\alpha_k^2<\infty$. Then
--   $$
--   \sum_{k=0}^\infty\alpha_k\|\nabla J(\theta_k)\|^2<\infty\quad\text{almost surely.} \qquad (A.26)
--   $$
--
--   Combined with the non-summability of the stepsizes, this forces $\|\nabla J(\theta_k)\|$ to be small infinitely often, which is the first half of the proof of Theorem 4.2.
--
--   **Formalization Note** The page's sum starts at $k=1$; summability does not depend on finitely many terms. The divergence condition $\sum_k\alpha_k=\infty$ of Assumption 4.1 is not needed here and is omitted, which makes the statement stronger. $\alpha_k>0$ is added. Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, App. A.3, p. 28, (A.26)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting
import Definitions.Def_RandomHorizonPG_Asymp_Estimator

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning MeasureTheory

/-- arXiv:1906.08383v3, (A.26), p. 28: along a run of Algorithm 3 with square-summable stepsizes,
`Σ_k α_k ‖∇J(θ_k)‖² < ∞` almost surely. -/
theorem weighted_gradient_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (α : ℕ → ℝ) (hα : ∀ k, 0 < α k) (θ₀ : EuclideanSpace ℝ (Fin d))
    (θ g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hrun : IsRPGRun P R γ π s₀ α θ₀ μ ℱ θ g)
    (hsq : Summable (fun k => α k ^ 2)) :
    ∀ᵐ ω ∂μ, Summable (fun k => α k * ‖gradient (objective P R γ π s₀) (θ k ω)‖ ^ 2) := by sorry

end RandomHorizonPG.Asymp
