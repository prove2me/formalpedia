-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_gaussianTraceclass_density
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.gaussianTraceclass_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:02:58.331641+00:00
-- url     : https://prove2.me/theorems/cfd63956-e2ac-4a9d-979a-b0204d08c6b8
-- title:
--   §2.1 equation (5): trace-class Gaussian density and entropy formula
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Let $D_1,D_2$ be covariances and suppose $T=D_2^{-1}-D_1^{-1}$ is trace class. The cylinder laws $\omega_{D_2}$ and $\omega_{D_1}$ are mutually absolutely continuous. With Fredholm determinants and the canonical $q_T$,
--
--   $$\frac{d\omega_{D_2}}{d\omega_{D_1}}(x)=\det(I+D_1T)^{1/2}e^{-q_T(x)/2},$$
--
--   $$\operatorname{Ent}(\omega_{D_2}\mid\omega_{D_1})=\tfrac12\operatorname{tr}\!\left(D_1T(I+D_1T)^{-1}\right)-\tfrac12\log\det(I+D_1T).$$
--
--   The determinant equals $\det(I+D_1^{1/2}TD_1^{1/2})=\det(D_1^{1/2}D_2^{-1}D_1^{1/2})>0$. Entropy uses the source nonpositive convention. Here $q_A$ is obtained by the Gaussian completion of finite-coordinate quadratic polynomials; it is not an arbitrary measurable extension from $K$. This supplies the sufficient trace-class density and entropy interface.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 4, §2.1 equation (5): trace-class Gaussian density and entropy formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- The valid trace-class sufficient condition and both formulas (5), PDF p.4.
No converse Feldman–Hájek criterion is asserted. -/
theorem gaussianTraceclass_density (e : ℕ ≃ G) (D1 D2 : RealCoordinateOperator G)
    (hD1 : IsCovariance D1) (hD2 : IsCovariance D2)
    (hT : IsModulusTraceClass (operatorInverse D2 - operatorInverse D1)) :
    let T := operatorInverse D2 - operatorInverse D1
    (cylinderGaussian D2 ≪ cylinderGaussian D1) ∧ (cylinderGaussian D1 ≪ cylinderGaussian D2) ∧
    0 < fredholmPlus (D1 * T) ∧
    fredholmPlus (D1 * T) = fredholmPlus (hilbertPositiveSqrt D1 * T * hilbertPositiveSqrt D1) ∧
    fredholmPlus (D1 * T) =
      fredholmPlus (hilbertPositiveSqrt D1 * operatorInverse D2 * hilbertPositiveSqrt D1 - 1) ∧
    (∀ᵐ x ∂cylinderGaussian D1, realRNDensity (cylinderGaussian D2) (cylinderGaussian D1) x =
      Real.sqrt (fredholmPlus (D1 * T)) * Real.exp (- gaussianQuadratic e T x / 2)) ∧
    nonpositiveRelativeEntropy (cylinderGaussian D2) (cylinderGaussian D1) =
      (((1 / 2 : ℝ) * basisOperatorTrace (D1 * T * operatorInverse (1 + D1 * T)) -
        (1 / 2 : ℝ) * Real.log (fredholmPlus (D1 * T)) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
