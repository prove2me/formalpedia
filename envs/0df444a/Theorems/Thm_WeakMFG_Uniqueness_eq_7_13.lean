-- Prove2me | Theorems.Thm_WeakMFG_Uniqueness_eq_7_13
-- name    : WeakMFG.Uniqueness.eq_7_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:14.197748+00:00
-- url     : https://prove2.me/theorems/ae3c3ba9-84a9-479a-8047-2a677c9ec800
-- title:
--   (7.13) — the Lasry–Lions gap has the same expectation under $P^{\mu^1,\alpha^1}$ and $P^{\mu^2,\alpha^2}$
-- statement:
--   Assume the standing assumptions (S), the joint measurability of the running reward, (U.2) $b(t,x,\mu,a)=b_0(t,x,a)$, the decomposition (U.3) $f=f_1(t,x,\mu)+f_2(t,\mu,q)+f_3(t,x,a)$, and (U.4) for this $f_1$. Let $\alpha^1,\alpha^2$ witness that $(\mu^1,q^1)$ and $(\mu^2,q^2)$ are solutions of the MFG (Definition 3.4, with $q^i$ measurable), and let $D^i$ be versions of $dP^{\mu^i,\alpha^i}/dP$. Then
--   $$0=\big[E^{\mu^1,\alpha^1}-E^{\mu^2,\alpha^2}\big]\Big[\Delta g(X)+\int_0^T\Delta f_1(t,X)\,dt\Big], \tag{7.13}$$
--   where $\Delta g(x)=g(x,\mu^1)-g(x,\mu^2)$, $\Delta f_1(t,x)=f_1(t,x,\mu^1)-f_1(t,x,\mu^2)$ and $E^{\mu^i,\alpha^i}[F]=E[D^iF]$.
--
--   The inequality $\ge 0$ comes from the optimality of the two controls, and $\le 0$ from (U.4), since $P^{\mu^i,\alpha^i}\circ X^{-1}=\mu^i$. The equality is the point where the monotonicity condition meets the control problem.
--
--   **Formalization Note.** The bracket $\Delta g(x)+\int_0^T\Delta f_1(t,x)\,dt$ is the defined quantity `lmGap g f₁ μ¹ μ² x` of the (U) definition file. The statement holds for every version of the densities.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §7.3, proof of Theorem 3.8, (7.13), p. 31

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_AssumptionU

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

/-- **(7.13)** (Carmona–Lacker, arXiv:1307.1152v2, §7.3, p. 31). Assume (U.2)
`b(t, x, μ, a) = b₀(t, x, a)`, the decomposition (U.3) `f = f₁(t, x, μ) + f₂(t, μ, q) + f₃(t, x, a)`,
and (U.4) for this `f₁`. Let `α¹, α²` witness that `(μ¹, q¹)` and `(μ², q²)` solve the MFG, and
let `Dⁱ` be versions of `dP^{μⁱ,αⁱ}/dP`. Then
`0 = [E^{μ¹,α¹} − E^{μ²,α²}][Δg(X) + ∫₀ᵀ Δf₁(t, X) dt]`,
with `Δg(x) = g(x, μ¹) − g(x, μ²)`, `Δf₁(t, x) = f₁(t, x, μ¹) − f₁(t, x, μ²)` and
`E^{μⁱ,αⁱ}[F] = E[Dⁱ F]`.
**Formalization Note.** `lmGap g f₁ μ¹ μ² x` is `Δg(x) + ∫₀ᵀ Δf₁(t, x) dt`. Conventions D1–D6 as in
`theorem_3_8`. -/
theorem eq_7_13 {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (ψ : WeakMFG.Existence.Path d T → ℝ) (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T)
    (hS : Standing B A σ b f g X Xp) (hD5 : FJointMeas A f)
    (b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ)) (hb₀ : ∀ t x μ a, b t x μ a = b₀ t x a)
    (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) (f₂ : ℝ≥0 → Ppsi ψ → PA A → ℝ)
    (f₃ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → ℝ) (hdec : IsU3Decomp f f₁ f₂ f₃) (hU4 : U4 g f₁)
    (μ₁ μ₂ : Ppsi ψ) (q₁ q₂ : ℝ≥0 → PA A)
    (hq₁ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₁)
    (hq₂ : @Measurable ℝ≥0 (PA A) _ (borel (PA A)) q₂)
    (α₁ α₂ : ℝ≥0 → Ω → EA)
    (hα₁ : IsMFGWitness B A σ b f g Xp μ₁ q₁ α₁) (hα₂ : IsMFGWitness B A σ b f g Xp μ₂ q₂ α₂)
    (D₁ D₂ : Ω → ℝ) (hD₁ : IsDensity B σ b Xp μ₁ α₁ D₁) (hD₂ : IsDensity B σ b Xp μ₂ α₂ D₂) :
    ∫ ω, D₁ ω * lmGap g f₁ μ₁ μ₂ (Xp ω) ∂B.P - ∫ ω, D₂ ω * lmGap g f₁ μ₁ μ₂ (Xp ω) ∂B.P = 0 := by sorry

end WeakMFG.Uniqueness
