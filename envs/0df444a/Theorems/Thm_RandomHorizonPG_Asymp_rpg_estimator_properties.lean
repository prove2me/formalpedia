-- Prove2me | Theorems.Thm_RandomHorizonPG_Asymp_rpg_estimator_properties
-- name    : RandomHorizonPG.Asymp.rpg_estimator_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:51:00.374442+00:00
-- url     : https://prove2.me/theorems/d32a92ec-87ba-439e-83fe-2b0e7f6e94bd
-- title:
--   Theorem 3.4 (∇̂J clauses), p. 10, with ℓ̂ of (A.19) — ∇̂J(θ) is unbiased, ‖∇J‖ ≤ B_ΘU_R/(1−γ)², ‖∇̂J‖ ≤ ℓ̂ a.s.
-- statement:
--   Let $(\mathcal S,\mathcal A,P,R,\gamma)$ be a finite discounted MDP with $\gamma\in(0,1)$, $s_0$ an initial state, and $\pi_\theta$ a parameterized policy satisfying Assumption 3.1. Fix $\theta\in\mathbb R^d$ and let $\hat\nabla J(\theta)$ be the stochastic policy gradient (3.8) of the RPG algorithm, with $T\sim\mathrm{Geom}(1-\gamma)$, $T'\sim\mathrm{Geom}(1-\gamma^{1/2})$ and EstQ's estimate $\hat Q$. Then:
--   1. the law of $\hat\nabla J(\theta)$ is a probability measure on $\mathbb R^d$ with finite mean;
--   2. $\hat\nabla J(\theta)$ is unbiased:
--   $$
--   \mathbb E\big[\hat\nabla J(\theta)\big]=\nabla J(\theta);
--   $$
--   3. the policy gradient is bounded: $\displaystyle\|\nabla J(\theta)\|\le\frac{B_\Theta U_R}{(1-\gamma)^2}$;
--   4. the estimate is almost surely bounded:
--   $$
--   \|\hat\nabla J(\theta)\|\le\hat\ell:=\frac{B_\Theta U_R}{(1-\gamma)(1-\gamma^{1/2})}\quad\text{a.s.} \qquad (A.19)
--   $$
--
--   These properties make the RPG update an unbiased stochastic gradient ascent with bounded steps, which is what the convergence analysis of Section 4 needs.
--
--   **Formalization Note** Only the clauses about $\hat\nabla J$ of (3.8), the estimator used by Algorithm 3, are stated; the clauses about $\check\nabla J$ (3.9) and $\tilde\nabla J$ (3.10) are not part of this item. Item 1 is implicit on the page ("the expectation is with respect to the random horizon $T'$, the trajectory … and the random sample $(s_T,a_T)$") and is stated explicitly, together with integrability, so that the mean is not Lean's default value for non-integrable functions. The expectation is the Bochner integral of the identity against the law `rpgLaw`. Finite state and action spaces.
-- source:
--   arXiv:1906.08383v3, Theorem 3.4, p. 10 (∇̂J clauses); (A.19), p. 26

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_RandomHorizonPG_Asymp_Setting
import Definitions.Def_RandomHorizonPG_Asymp_Estimator

namespace RandomHorizonPG.Asymp

open FoundationsML.ReinforcementLearning MeasureTheory

/-- arXiv:1906.08383v3, Theorem 3.4, p. 10 (the `∇̂J` clauses), with `ℓ̂` of (A.19), p. 26: for
every `θ`, the law of the stochastic gradient `∇̂J(θ)` of (3.8) is a probability measure with
finite mean equal to `∇J(θ)`; `‖∇J(θ)‖ ≤ B_Θ U_R/(1−γ)²`; and
`‖∇̂J(θ)‖ ≤ ℓ̂ = B_Θ U_R/((1−γ)(1−γ^{1/2}))` almost surely. -/
theorem rpg_estimator_properties {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (R : S → A → ℝ) (γ UR LΘ BΘ : ℝ)
    (π : EuclideanSpace ℝ (Fin d) → S → A → ℝ) (s₀ : S)
    (hP : IsTransitionKernel P) (hγ : 0 < γ ∧ γ < 1) (hA : Assumption31 R UR π LΘ BΘ) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      IsProbabilityMeasure (rpgLaw P R γ π s₀ θ) ∧
      Integrable id (rpgLaw P R γ π s₀ θ) ∧
      ∫ x, x ∂(rpgLaw P R γ π s₀ θ) = gradient (objective P R γ π s₀) θ ∧
      ‖gradient (objective P R γ π s₀) θ‖ ≤ BΘ * UR / (1 - γ) ^ 2 ∧
      ∀ᵐ x ∂(rpgLaw P R γ π s₀ θ), ‖x‖ ≤ BΘ * UR / ((1 - γ) * (1 - Real.sqrt γ)) := by sorry

end RandomHorizonPG.Asymp
