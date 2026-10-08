-- Prove2me | Theorems.Thm_StochConvexProg_FirstStage_proposition_1
-- name    : StochConvexProg.FirstStage.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:35.239913+00:00
-- url     : https://prove2.me/theorems/074f550f-e6cc-4442-a1d6-9a5223844d31
-- title:
--   Proposition 1 — for a normal convex integrand, inf over ℒᵖ of ∫ h(s, z(s)) equals ∫ inf h(s, ·)
-- statement:
--   Let $(S,\Sigma,\sigma)$ be a probability space and let $h$ be a normal convex integrand on $S\times\mathbb R^n$. Then $s\mapsto\inf_{z\in\mathbb R^n}h(s,z)$ is measurable, and
--   $$\inf_{z\in\mathcal L^p_n}\int_S h\big(s,z(s)\big)\,\sigma(ds)=\int_S\Big[\inf_{z\in\mathbb R^n}h(s,z)\Big]\,\sigma(ds)$$
--   for every $p\in[1,+\infty]$ such that the infimum on the left is not $+\infty$. Both integrals are taken under the convention (2.4).
--
--   This interchange of infimum and integral is the tool that converts the first-stage function $J$, an infimum over recourse functions, into the integral of the pointwise optimal recourse cost.
--
--   **Formalization Note** $\mathcal L^p_n$ is `Lp (Fin n → ℝ) p σ`, with $p$ an extended nonnegative real with $1\le p$ ($p=\infty$ included); $z(s)$ is the canonical measurable representative of the class $z$. The integral under the convention (2.4) is the published definition `DupacovaWets.Consistency.expect`: $+\infty$ if $\int\theta^+\,d\sigma=\infty$, and $\int\theta^+\,d\sigma-\int\theta^-\,d\sigma$ (real or $-\infty$) otherwise, with lower Lebesgue integrals of the positive and negative parts; for a measurable $\theta$, $\int\theta^+<\infty$ holds exactly when $\theta$ is majorized almost everywhere by a summable function, so this is the paper's convention.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 181, Proposition 1, (2.5)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_StochConvexProg_FirstStage_NormalIntegrand

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Proposition 1, p. 181: for a normal convex integrand `h` on `S × Rⁿ`, `s ↦ inf_z h(s, z)` is
measurable, and `inf_{z ∈ ℒᵖ_n} ∫_S h(s, z(s)) σ(ds) = ∫_S [inf_{z ∈ Rⁿ} h(s, z)] σ(ds)` for every
`p ∈ [1, +∞]` such that the left-hand infimum is not `+∞`. -/
theorem proposition_1 {S : Type*} [MeasurableSpace S] {σ : Measure S} [IsProbabilityMeasure σ]
    {n : ℕ} (h : S → (Fin n → ℝ) → EReal) (hh : IsNormalConvexIntegrand h) :
    Measurable (fun s => ⨅ z : Fin n → ℝ, h s z) ∧
      ∀ p : ENNReal, 1 ≤ p →
        (⨅ z : Lp (Fin n → ℝ) p σ, DupacovaWets.Consistency.expect σ (fun s => h s (z s))) ≠ ⊤ →
        (⨅ z : Lp (Fin n → ℝ) p σ, DupacovaWets.Consistency.expect σ (fun s => h s (z s))) =
          DupacovaWets.Consistency.expect σ (fun s => ⨅ z : Fin n → ℝ, h s z) := by sorry

end StochConvexProg.FirstStage
