-- Prove2me | Theorems.Thm_PDSmooth_Framework_lemma_4_3
-- name    : PDSmooth.Framework.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:40.610607+00:00
-- url     : https://prove2.me/theorems/764a882e-9bc8-4e25-b727-773679dc6591
-- title:
--   Lemma 4.3, p. 15 — ‖prox(q_ρ,x,λ) − prox(q,x,λ)‖ ≤ 2√(ρR_Y(ω_Y)/(λ⁻¹ − γ)) (Eq. (4.12), ρ ≥ 0)
-- statement:
--   Under the standing assumptions of problem (1.1), let $0<\lambda<\gamma^{-1}$, $\rho\ge0$ and $x\in\mathcal X$. If $p=\mathrm{prox}(q,x,\lambda)$ and $p_\rho=\mathrm{prox}(q_\rho,x,\lambda)$ are Bregman proximal points (with respect to $\omega_{\mathcal X}$, over $\mathcal X$) of the original and the dually smoothed objective, then
--
--   $$
--   \|p_\rho-p\|\le 2\sqrt{\frac{\rho\,R_{\mathcal Y}(\omega_{\mathcal Y})}{\lambda^{-1}-\gamma}} .
--   $$
--
--   Dual smoothing moves the proximal point by at most this amount; with $\rho=2\eta/R_{\mathcal Y}(\omega_{\mathcal Y})$ the bound becomes $2\sqrt{2\eta/(\lambda^{-1}-\gamma)}$ (the paper's (4.13)). Combined with Lemma 4.2 it yields Theorem 4.1.
--
--   **Formalization Note** This is the paper's (4.12). The lemma's "for any $\eta>0$" plays no role in (4.12), where $\eta$ does not occur; the specialization (4.13) is the substitution $\rho=2\eta/R_{\mathcal Y}(\omega_{\mathcal Y})$, $x=x_K$ and is not stated separately. The paper takes $\rho>0$; $\rho\ge0$ adds the trivial case $\rho=0$.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 15, Lemma 4.3, (4.12)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Lemma 4.3, (4.12), p. 15: for `ρ ≥ 0` and `x ∈ X`,
`‖prox(q_ρ, x, λ) − prox(q, x, λ)‖ ≤ 2√(ρ R_Y(ω_Y)/(λ⁻¹ − γ))`. -/
theorem lemma_4_3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ρ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X)
    (p pρ : E) (hp : IsProx (qObj Φ g r Y) ωX X lam x p)
    (hpρ : IsProx (qSmooth Φ g r ωY Y ρ) ωX X lam x pρ) :
    ‖pρ - p‖ ≤ 2 * Real.sqrt (ρ * rangeY ωY Y / (lam⁻¹ - γ)) := by sorry
end PDSmooth.Framework
