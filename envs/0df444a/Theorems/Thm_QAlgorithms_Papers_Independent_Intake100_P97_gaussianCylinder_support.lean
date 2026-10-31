-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_gaussianCylinder_support
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.gaussianCylinder_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:01:16.576+00:00
-- url     : https://prove2.me/theorems/92f45916-71cf-4a6d-881a-4ff8694eda46
-- title:
--   §2.1 unnumbered: Gaussian cylinder law and weighted support
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. For every covariance $D$ there is a unique Borel probability $\omega_D$ with the following finite-dimensional cylinder densities. If $I\subset\Gamma$ is finite and $D_I=[(\delta_i,D\delta_j)]_{i,j\in I}$, then its $I$-coordinate marginal has density
--
--   $$\frac{\exp(-x^TD_I^{-1}x/2)}{\sqrt{(2\pi)^{|I|}\det D_I}}.$$
--
--   It is also uniquely determined among Borel probabilities by $\int_X e^{i(y,x)}\,d\omega_D=e^{-(y,Dy)/2}$ for $y\in X_l^*$. Moreover,
--
--   $$\int_X\sum_n l_nx_n^2\,d\omega_D=\sum_n l_nD_{nn}\le\|D\|,\qquad\omega_D(X\setminus X_l)=0.$$
--
--   The nonnegative integral is finite, and the weighted quadratic sum is integrable. This constructs the classical Gaussian phase-space law even when $D$ is not trace class on $K$.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 4, §2.1 unnumbered: Gaussian cylinder law and weighted support

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Gaussian cylinder law, uniqueness, characteristic function, and weighted support;
§2.1 and (4), PDF pp.3–4. -/
theorem gaussianCylinder_support [Countable G] [Infinite G] (l : G → ℝ) (hl : IsWeight l)
    (D : RealCoordinateOperator G) (hD : IsCovariance D) :
    IsCylinderGaussian (cylinderGaussian D) D ∧
    (∀ mu, IsCylinderGaussian mu D → mu = cylinderGaussian D) ∧
    (∀ y : RealCoordinateHilbert G, inDual l y →
      (∫ x, Complex.exp (Complex.I * ((∑' i, y i * x i : ℝ) : ℂ)) ∂cylinderGaussian D) =
        Complex.exp ((- inner ℝ y (D y) / 2 : ℝ) : ℂ)) ∧
    (∀ mu : Measure (CylinderPhase G), IsProbabilityMeasure mu →
      (∀ y : RealCoordinateHilbert G, inDual l y →
        (∫ x, Complex.exp (Complex.I * ((∑' i, y i * x i : ℝ) : ℂ)) ∂mu) =
          Complex.exp ((- inner ℝ y (D y) / 2 : ℝ) : ℂ)) → mu = cylinderGaussian D) ∧
    (∫⁻ x, weightedEnergy l x ∂cylinderGaussian D) =
      ∑' i, ENNReal.ofReal (l i * entry D i i) ∧
    (∫⁻ x, weightedEnergy l x ∂cylinderGaussian D) ≤ ENNReal.ofReal ‖D‖ ∧
    Integrable (fun x => ∑' i, l i * (x i) ^ 2) (cylinderGaussian D) ∧
    (∫ x, ∑' i, l i * (x i) ^ 2 ∂cylinderGaussian D) = ∑' i, l i * entry D i i ∧
    (∑' i, l i * entry D i i) ≤ ‖D‖ ∧
    (cylinderGaussian D) {x | ¬ inWeighted l x} = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
