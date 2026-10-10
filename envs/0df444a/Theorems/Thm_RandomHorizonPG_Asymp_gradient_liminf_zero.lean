-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_gradient_liminf_zero
-- name    : RandomHorizonPG.Asymp.gradient_liminf_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:38.015983+00:00
-- url     : https://prove2.me/theorems/49af0e89-048a-4c89-a579-44e609ac68fc
-- title:
--   (A.27), p. 28 — along an RPG run under Assumption 4.1, liminf_{k→∞} ‖∇J(θ_k)‖ = 0 almost surely
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1. Let $(\theta_k)$ be a run of Algorithm 3 (RPG) with positive stepsizes satisfying the Robbins–Monro condition $\sum_k\alpha_k=\infty$, $\sum_k\alpha_k^2<\infty$ (Assumption 4.1). Then almost surely
--   $$
--   \liminf_{k\to\infty}\|\nabla J(\theta_k)\|=0. \qquad (A.27)
--   $$
--
--   This is the intermediate step of the proof of Theorem 4.2; the remaining step upgrades the lim inf to a limit.
--
--   **Formalization Note** The lim inf is written as: for every $\varepsilon>0$ and every $N$ there is $k\ge N$ with $\|\nabla J(\theta_k)\|<\varepsilon$. The page prints no "a.s." on (A.27); it follows from (A.26), which holds almost surely, and "almost surely" is the reading. $\alpha_k>0$ is added. Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, App. A.3, p. 28, (A.27)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting
import Definitions.Def_RandomHorizonPG_Asymp_Estimator

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning MeasureTheory Filter

/-- arXiv:1906.08383v3, (A.27), p. 28: along a run of Algorithm 3 under Assumption 4.1,
`liminf_{k→∞} ‖∇J(θ_k)‖ = 0` almost surely. -/
theorem gradient_liminf_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (α : ℕ → ℝ) (hα : ∀ k, 0 < α k) (θ₀ : EuclideanSpace ℝ (Fin d))
    (θ g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hrun : IsRPGRun P R γ π s₀ α θ₀ μ ℱ θ g)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, α k) atTop atTop)
    (hsq : Summable (fun k => α k ^ 2)) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N,
      ‖gradient (objective P R γ π s₀) (θ k ω)‖ < ε := by sorry

end RandomHorizonPG.Asymp
