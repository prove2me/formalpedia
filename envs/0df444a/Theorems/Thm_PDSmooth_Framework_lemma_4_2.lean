-- Prove2me | Theorems.Thm_PDSmooth_Framework_lemma_4_2
-- name    : PDSmooth.Framework.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:36.630797+00:00
-- url     : https://prove2.me/theorems/0ba983ca-2656-4d5d-9dab-54a9f87ef4b9
-- title:
--   Lemma 4.2, p. 15 — at the stopping iteration K, ‖x_K − prox(q_ρ, x_K, λ)‖ ≤ 2√(2η/(λ⁻¹ − γ))
-- statement:
--   Under the standing assumptions of problem (1.1), let $\eta>0$, $0<\lambda<\gamma^{-1}$ and $\rho=2\eta/R_{\mathcal Y}(\omega_{\mathcal Y})$, and let $(x_k)_{k\ge1}$ be a run of Algorithm 1. Let $K\ge1$ be the iteration at which Algorithm 1 terminates, i.e. the first $k\ge1$ at which the stopping test (4.6) holds. Then every Bregman proximal point $p=\mathrm{prox}(q_\rho,x_K,\lambda)$ satisfies
--
--   $$
--   \|x_K-p\|\le 2\sqrt{\frac{2\eta}{\lambda^{-1}-\gamma}} .
--   $$
--
--   The output of Algorithm 1 is therefore a near-stationary point of the dually smoothed objective $q_\rho$; it is the first half of Approach I.
--
--   **Formalization Note** "The iteration at which Algorithm 1 terminates" is encoded as: (4.6) holds at $K$ and fails at every $j\in[1,K)$. The statement quantifies over every proximal point rather than assuming one exists.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 15, Lemma 4.2

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Lemma 4.2, p. 15: at the iteration `K` at which Algorithm 1 terminates (the first `K ≥ 1`
at which (4.6) holds), `‖x_K − prox(q_ρ, x_K, λ)‖ ≤ 2√(2η/(λ⁻¹ − γ))`, with `ρ = 2η/R_Y(ω_Y)`. -/
theorem lemma_4_2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam η : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hη : 0 < η)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x)
    (K : ℕ) (hK1 : 1 ≤ K) (hKstop : Stops γ lam η x K)
    (hKfirst : ∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j)
    (p : E) (hp : IsProx (qSmooth Φ g r ωY Y (2 * η / rangeY ωY Y)) ωX X lam (x K) p) :
    ‖x K - p‖ ≤ 2 * Real.sqrt (2 * η / (lam⁻¹ - γ)) := by sorry
end PDSmooth.Framework
