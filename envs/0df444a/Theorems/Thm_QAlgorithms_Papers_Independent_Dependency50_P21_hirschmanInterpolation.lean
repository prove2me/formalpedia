-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanInterpolation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.hirschmanInterpolation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:09:50.051925+00:00
-- url     : https://prove2.me/theorems/8b406783-7cb6-4a64-ba0c-2ecb4764b97f
-- title:
--   Hirschman interpolation for Schatten norms
-- statement:
--   Let H be a finite-dimensional complex Hilbert space, as in Step 1 of the proof. Let S={z in C: 0≤Re z≤1}, and let G:S→L(H) be bounded, holomorphic in the open strip, and continuous up to its boundary. Fix 0<θ<1 and p₀,p₁∈[1,∞], and define 1/pθ=(1−θ)/p₀+θ/p₁, with 1/∞=0. Let αθ and βθ be the densities in (28), namely
--
--   $$\alpha_\theta(t)=\frac{\sin(\pi\theta)}{2(1-\theta)(\cosh(\pi t)-\cos(\pi\theta))},\qquad \beta_\theta(t)=\frac{\sin(\pi\theta)}{2\theta(\cosh(\pi t)+\cos(\pi\theta))}.$$
--
--   Then
--
--   $$\log\|G(\theta)\|_{p_\theta}\le\int_{\mathbb R}\!\left[\alpha_\theta(t)\log\bigl(\|G(it)\|_{p_0}^{1-\theta}\bigr)+\beta_\theta(t)\log\bigl(\|G(1+it)\|_{p_1}^{\theta}\bigr)\right]dt.$$
--
--   The norm at infinity is the operator norm. Logarithms are natural, log(0)=−∞, and the integral is the extended signed integral whose positive part is finite. This is the interpolation inequality used in the recovery theorem.
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 8, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Lemma 3.2, PDF p.8, Eq.(27), Appendix A pp.20-21. H is finite-dimensional
as in Step 1, p.7. Both powers 1-theta and theta in the printed logarithms are retained.
Zero norms have extended logarithm -infinity; p=infinity is the operator norm. -/
theorem hirschmanInterpolation {I : Type*} [Fintype I] [DecidableEq I]
    (G : ℂ → Mat I)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (theta : ℝ) (htheta : 0 < theta ∧ theta < 1)
    (p0 p1 : ℝ≥0∞) (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) :
    extendedLog (schattenNorm (interpolationExponent theta p0 p1) (G (theta : ℂ))) ≤
      upperLogIntegral (fun t =>
        (alphaDensity theta t : EReal) *
          extendedLog ((schattenNorm p0 (G ((t : ℂ) * Complex.I))) ^ (1 - theta)) +
        (betaDensity theta t : EReal) *
          extendedLog ((schattenNorm p1 (G (1 + (t : ℂ) * Complex.I))) ^ theta)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end
