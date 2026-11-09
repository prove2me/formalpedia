-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_fact_A_1
-- name    : TusnadyPlane.RandomPoints.fact_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:16.318958+00:00
-- url     : https://prove2.me/theorems/94b2e1d7-4321-49f4-a8e1-42908f84b7df
-- title:
--   Fact A.1 — Bounded differences
-- statement:
--   Let $\xi_1,\ldots,\xi_n$ be independent measurable random variables with arbitrary measurable value spaces, and let $\Gamma$ be a measurable random element independent of their whole vector. Suppose $f=\varphi(\Gamma,\xi_1,\ldots,\xi_n)$ is integrable, $\varphi$ is measurable, and changing one coordinate changes $\varphi(\gamma,\cdot)$ by at most a common $c>0$, for every $\gamma$. For every real $t$,
--   $$\mathbb E[\exp(t(f-\mathbb E[f\mid\Gamma]))\mid\Gamma]\le\exp(nt^2c^2/2)\quad\text{almost surely}.$$
--   The centered exponential is integrable, as is implicit in this finite conditional-MGF bound. No boundedness of $\Gamma$ or $f$, finite-valued assumption, or standard Borel restriction is imposed. This supplies the conditional concentration input for the actual digit fluctuation.
--
--   Differences from the source:
--   - encoding: arbitrary independent random variables and independent background random element → measurable maps into arbitrary, possibly different, measurable spaces; IndepFun of Γ and the whole vector, and comap sigma(Γ); reason: these express exactly the source independence and conditioning without adding regular conditional distribution assumptions
--   - encoding: finite conditional exponential-moment bound → integrability of the centered exponential is included in the conclusion alongside the almost-sure bound; reason: finite moments are genuine; integrability follows from bounded differences and is not an extra hypothesis
--   - encoding: changing one coordinate → two dependent vectors equal at every other coordinate; reason: this is the same pointwise bounded-differences condition for every background value, with indices in Fin n
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 14 (PDF p. 15), Fact A.1, Appendix A.2

import Mathlib
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Fact A.1, printed p.14 / PDF p.15. No standard-Borel or bounded-data restriction. -/
theorem fact_A_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) {B : Type*} [MeasurableSpace B]
    {E : Fin n → Type*} [∀ i, MeasurableSpace (E i)]
    (Γ : Ω → B) (ξ : (i : Fin n) → Ω → E i)
    (hΓ : Measurable Γ) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hbackground : IndepFun Γ (fun ω i => ξ i ω) μ)
    (φ : B × ((i : Fin n) → E i) → ℝ) (hφ : Measurable φ)
    (hint : Integrable (fun ω => φ (Γ ω, fun i => ξ i ω)) μ)
    (c : ℝ) (hc : 0 < c)
    (hchange : ∀ (γ : B) (x y : (i : Fin n) → E i) (i : Fin n),
      (∀ k, k ≠ i → x k = y k) → |φ (γ,x) - φ (γ,y)| ≤ c) (t : ℝ) :
    let f := fun ω => φ (Γ ω, fun i => ξ i ω)
    let H := MeasurableSpace.comap Γ inferInstance
    Integrable (fun ω => Real.exp (t * (f ω - condExp H μ f ω))) μ ∧
    ∀ᵐ ω ∂μ,
      condExp H μ (fun v => Real.exp (t * (f v - condExp H μ f v))) ω ≤
        Real.exp ((n : ℝ)*t^2*c^2/2) := by sorry

end TusnadyPlane.RandomPoints
