-- Prove2me | Theorems.Thm_TusnadyPlane_RandomPoints_fact_2_2
-- name    : TusnadyPlane.RandomPoints.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:11.967197+00:00
-- url     : https://prove2.me/theorems/19d49b4e-d730-4c7c-9870-742032a343f9
-- title:
--   Fact 2.2 — Sums of symmetric variables
-- statement:
--   Let $X_1,\ldots,X_m$ be independent measurable real random variables on any probability space. Suppose each has the same distribution as its negative and, for a common $\sigma>0$, has finite second and fourth moments with $\mathbb E X_i^2=\sigma^2$ and $\mathbb E X_i^4\le3\sigma^4$. Then, for every real shift $\theta$,
--   $$\mathbb E\left|\theta+\sum_{i=1}^mX_i\right|\ge\sigma\sqrt{m/3}.$$
--   The assertion includes $m=0$ and arbitrary symmetric real laws, rather than only random signs. It is the general moment bound used by the local experiment.
--
--   Differences from the source:
--   - encoding: random variables with finite second and fourth moments and symmetry in law → explicit measurability, integrability of the second and fourth powers, and equality of pushforward measures for X and -X; reason: these express genuine finite moments and symmetry; default nonintegrable Bochner values cannot satisfy the intended moment convention
--   - encoding: indices 1 through m → Fin m with real m/3; reason: finite relabeling includes m=0 and preserves the real square-root argument
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 6 (PDF p. 7), Fact 2.2; proof Appendix A.1, printed p.14 (PDF p.15)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace TusnadyPlane.RandomPoints

/-- Fact 2.2, printed p.6 / PDF p.7; finite moments are genuine integrals. -/
theorem fact_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hsym : ∀ i, Measure.map (X i) μ = Measure.map (fun ω => -X i ω) μ)
    (σ : ℝ) (hσ : 0 < σ)
    (hint2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (hint4 : ∀ i, Integrable (fun ω => (X i ω)^4) μ)
    (hsecond : ∀ i, (∫ ω, (X i ω)^2 ∂μ) = σ^2)
    (hfourth : ∀ i, (∫ ω, (X i ω)^4 ∂μ) ≤ 3*σ^4) (θ : ℝ) :
    σ * Real.sqrt ((m : ℝ)/3) ≤ ∫ ω, |θ + ∑ i : Fin m, X i ω| ∂μ := by sorry

end TusnadyPlane.RandomPoints
