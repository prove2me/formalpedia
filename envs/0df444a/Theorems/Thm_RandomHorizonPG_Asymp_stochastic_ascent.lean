-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_stochastic_ascent
-- name    : RandomHorizonPG.Asymp.stochastic_ascent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:31.343253+00:00
-- url     : https://prove2.me/theorems/d44e11cf-c612-44cb-9c4c-5afec98331d2
-- title:
--   Lemma A.1, p. 27 — stochastic ascent (A.23); W_k = J(θ_k) − Lℓ̂² Σ_{j≥k} α_j² is a bounded submartingale with (A.24)
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1. Let $(\theta_k)$ be a run of Algorithm 3 (RPG) with positive, square-summable stepsizes $\alpha_k$ ($\sum_k\alpha_k^2<\infty$) on a probability space with filtration $(\mathcal F_k)$. Let $L$ be the constant (3.6) and $\hat\ell=B_\Theta U_R/((1-\gamma)(1-\gamma^{1/2}))$ the constant (A.19), and define
--   $$
--   W_k=J(\theta_k)-L\hat\ell^2\sum_{j=k}^\infty\alpha_j^2. \qquad (A.22)
--   $$
--   Then for every $k$, almost surely,
--   $$
--   \mathbb E[J(\theta_{k+1})\mid\mathcal F_k]\ge J(\theta_k)+\mathbb E[(\theta_{k+1}-\theta_k)\mid\mathcal F_k]^\top\nabla J(\theta_k)-L\alpha_k^2\hat\ell^2, \qquad (A.23)
--   $$
--   $$
--   \mathbb E[W_{k+1}\mid\mathcal F_k]\ge W_k+\alpha_k\|\nabla J(\theta_k)\|^2, \qquad (A.24)
--   $$
--   and $(W_k)$ is a bounded submartingale with respect to $(\mathcal F_k)$.
--
--   This is the stochastic ascent property behind Theorem 4.2: the submartingale convergence theorem applied to $(W_k)$ yields the almost sure summability (A.26).
--
--   **Formalization Note** The page prints the tail of (A.22) as $\sum_{j=k}^\infty\alpha_k^2$, which diverges unless $\alpha_k=0$; the text that follows ("$\{\alpha_k\}$ is square-summable, we conclude that $W_k$ is bounded") requires the intended $\sum_{j\ge k}\alpha_j^2$, which is what is stated. Conditional expectations are Mathlib's `condExp`; every function involved is bounded and measurable. $\alpha_k>0$ is added (the page's proofs divide by $\alpha_k$ and need $\alpha_k\|\nabla J\|^2\ge0$). Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, App. A.3, p. 27, (A.22), Lemma A.1, (A.23)–(A.24)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting
import Definitions.Def_RandomHorizonPG_Asymp_Estimator

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning MeasureTheory

/-- arXiv:1906.08383v3, Lemma A.1 with (A.22), p. 27: along a run of Algorithm 3, with
`L` of (3.6) and `ℓ̂` of (A.19), the stochastic ascent property (A.23) holds, and
`W_k = J(θ_k) − L ℓ̂² Σ_{j ≥ k} α_j²` is a bounded submartingale with (A.24)
`E[W_{k+1} | ℱ_k] ≥ W_k + α_k ‖∇J(θ_k)‖²`. The tail of (A.22) is read as `Σ_{j≥k} α_j²`. -/
theorem stochastic_ascent {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ)
    {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (α : ℕ → ℝ) (hα : ∀ k, 0 < α k) (θ₀ : EuclideanSpace ℝ (Fin d))
    (θ g : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hrun : IsRPGRun P R γ π s₀ α θ₀ μ ℱ θ g)
    (hsq : Summable (fun k => α k ^ 2)) :
    let L : ℝ := UR * LΘ / (1 - γ) ^ 2 + (1 + γ) * UR * BΘ ^ 2 / (1 - γ) ^ 3
    let ℓ : ℝ := BΘ * UR / ((1 - γ) * (1 - Real.sqrt γ))
    let W : ℕ → Ω → ℝ := fun k ω =>
      objective P R γ π s₀ (θ k ω) - L * ℓ ^ 2 * ∑' j : ℕ, α (k + j) ^ 2
    (∀ k, (fun ω => objective P R γ π s₀ (θ k ω) +
          inner ℝ ((μ[fun ω => θ (k + 1) ω - θ k ω | ℱ k]) ω)
            (gradient (objective P R γ π s₀) (θ k ω)) - L * α k ^ 2 * ℓ ^ 2)
        ≤ᵐ[μ] μ[fun ω => objective P R γ π s₀ (θ (k + 1) ω) | ℱ k]) ∧
    (∀ k, (fun ω => W k ω + α k * ‖gradient (objective P R γ π s₀) (θ k ω)‖ ^ 2)
        ≤ᵐ[μ] μ[W (k + 1) | ℱ k]) ∧
    (∃ C : ℝ, ∀ k ω, |W k ω| ≤ C) ∧ Submartingale W ℱ μ := by sorry

end RandomHorizonPG.Asymp
