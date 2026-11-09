-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_outer_construction
-- name    : PrivateContinualCounting.Kraft.outer_construction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:09.940499+00:00
-- url     : https://prove2.me/theorems/0847ff57-d1f8-4417-8bee-a9d4e31964ba
-- title:
--   §3.3 and Appendix C — the canonical outer construction
-- statement:
--   Let $g\in\mathcal G$ satisfy $K(g)$, and let $f$ and $h$ be the canonical piecewise spectral weight and normalized positive outer integral defined above. Then $f$ is positive and measurable, and $f$, $\log f$ and $f^{-1}$ are integrable for normalized circle measure. The function $h$ is analytic and zero-free in the disk. Both $h$ and $1/h$ are outer elements of $H^2$, their Taylor coefficients are real, and the Taylor series for $h$, $r=1/h$ and $l=h/(1-z)$ converge to those functions throughout the disk. The coefficients of $l$ are prefix sums of those of $h$. Almost everywhere, $|h^*|^2=f$ and $|r^*|^2=f^{-1}$. In particular, the constructed real scalar coefficients are admissible LTI factors and
--   $$\|h\|_{H^2}^2=\int f\,dm,\qquad
--   \Delta^2=\|r\|_{H^2}^2=\int f^{-1}\,dm
--   =\frac1\pi\int_1^\infty\frac{du}{u g(u)}+\frac{e-\pi^{-1}}{g(1)}<\infty.$$
--   This item records the paper's unnumbered construction obligations separately from the four numbered milestones. No final bound, boundary formula, realness or spectral factorization is assumed in the definition layer.
--
--   Differences from the source:
--   - encoding: g defined on the real half-line [1,∞) → g is a function on ℝ with every envelope condition restricted to [1,∞); reason: Values below 1 are unused in all claims; monotonicity and doubling allow discontinuities.
--   - encoding: analytic functions, Hardy norms and almost-everywhere boundary values → derivative-defined Taylor coefficients; reused coefficient-space H²/outer predicates; explicit summability, integrability and boundary identities in the conclusion; reason: These are the same analytic objects; the reused negative-angle boundary is evaluated at -θ to give the source positive-angle convention.
--   - encoding: real coefficients of h and 1/h, with l=h/(1-z) → the real candidate uses real parts and the theorem proves all discarded imaginary parts vanish; reason: No complex information is discarded by assumption; admissibility is a conclusion.
--   - encoding: spectral weight on the circle parameter interval (-π,π] → the real-line piecewise weight uses the same constant g(1)/e outside that interval; reason: All analytic integrals use restricted circle measure; the additionally stated positivity outside the interval is immediate from this extension and changes no source instance.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 8, PDF p. 10, §3.3, Kraft sufficiency, unnumbered construction; Kisung Park, STOC 2027 submission #86 (October 2026), p. 20, PDF p. 22, Appendix C, The spectral weight and Outer functions

import Definitions.Def_PrivateContinualCounting_Kraft_SpectralConstruction

open MeasureTheory Filter Complex

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- The unnumbered construction in §3.3 and Appendix C. Every analytic identity is
an obligation here, never constructor data or an assumption about the envelope. -/
theorem outer_construction (g : ℝ → ℝ) (hg : IsEnvelope g) (hK : KraftCondition g) :
    (∀ θ : ℝ, 0 < spectralWeight g θ) ∧
    Measurable (spectralWeight g) ∧
    Integrable (spectralWeight g) circleMeasure ∧
    Integrable (fun θ => Real.log (spectralWeight g θ)) circleMeasure ∧
    Integrable (fun θ => 1 / spectralWeight g θ) circleMeasure ∧
    IntegrableOn (fun u : ℝ => 1 / (u * g u)) (Set.Ici 1) ∧
    AnalyticOnNhd ℂ (outerFunction g) (Metric.ball 0 1) ∧
    (∀ z : ℂ, ‖z‖ < 1 → outerFunction g z ≠ 0) ∧
    InfoShareH2.IsOuter (outerCoeff g) ∧
    InfoShareH2.IsOuter (strategyCoeff g) ∧
    (∀ n : ℕ, (outerCoeff g n).im = 0 ∧ (strategyCoeff g n).im = 0 ∧
      (decoderCoeff g n).im = 0) ∧
    (∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n => outerCoeff g n * z ^ n) (outerFunction g z) ∧
      HasSum (fun n => strategyCoeff g n * z ^ n) (1 / outerFunction g z) ∧
      HasSum (fun n => decoderCoeff g n * z ^ n) (outerFunction g z / (1 - z))) ∧
    (∀ n : ℕ, decoderCoeff g n = ∑ j ∈ Finset.range (n + 1), outerCoeff g j) ∧
    (∀ᵐ θ ∂circleMeasure, ‖positiveBoundary (outerCoeff g) θ‖ ^ 2 = spectralWeight g θ) ∧
    (∀ᵐ θ ∂circleMeasure, ‖positiveBoundary (strategyCoeff g) θ‖ ^ 2 = 1 / spectralWeight g θ) ∧
    hardyNormSq (outerCoeff g) = (∫ θ, spectralWeight g θ ∂circleMeasure) ∧
    IsLTI (constructedData g) ∧
    (constructedData g).deltaSq = hardyNormSq (strategyCoeff g) ∧
    hardyNormSq (strategyCoeff g) = (∫ θ, 1 / spectralWeight g θ ∂circleMeasure) ∧
    (∫ θ, 1 / spectralWeight g θ ∂circleMeasure) =
      (1 / Real.pi) * (∫ u in Set.Ici (1 : ℝ), 1 / (u * g u)) +
      (Real.exp 1 - 1 / Real.pi) / g 1 := by sorry

end PrivateContinualCounting.Kraft
