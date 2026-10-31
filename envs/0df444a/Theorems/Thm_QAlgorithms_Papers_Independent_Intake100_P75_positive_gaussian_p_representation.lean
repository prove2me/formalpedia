-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_positive_gaussian_p_representation
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.positive_gaussian_p_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:04:08.666972+00:00
-- url     : https://prove2.me/theorems/2991c7bb-76cd-4f7e-99af-4f93f16a19f7
-- title:
--   Positive Gaussian coherent-product representation
-- statement:
--   Let $\rho$ be a normalized two-mode Gaussian density with full anticommutator covariance $M$ in the interleaved quadrature order; vacuum has covariance $I_4$. Suppose $M-I_4$ is positive semidefinite. Then there are a first-moment vector $d\in\mathbb R^4$ and a Gaussian probability measure $\mu$ with mean $d$ and classical covariance $(M-I_4)/2$ such that
--
--   $$
--   \rho=\int_{\mathbb R^4}|\alpha_1(x),\alpha_2(x)\rangle\langle\alpha_1(x),\alpha_2(x)|\,d\mu(x),\qquad
--   \alpha_j(x)=\frac{x_j+ip_j}{\sqrt2}.
--   $$
--
--   The coherent-product state map is measurable in the trace-norm state space and has the actual operator barycenter $\rho$. Consequently $\rho$ is separable. Singular Gaussian laws, including the vacuum Dirac law, are allowed. This records the Fourier/positive-P implication in the main proof independently of the undefined boundary gain of Theorem 2.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 1, Announcement on p.1; explicit proof implication, Eqs. (18)–(19), pp.4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P75

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P75

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable IsBarycenter rankOne productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance standardFormCovariance
   modeCovarianceBlock productWeyl CharacteristicSummable multimodeWeylTrace
   covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Next46.P45
  (TwoMode PureVector Decomposes ladderCoefficients squeezedVector
   squeezedCoefficients GaussianShiftLaw shiftArgument)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel partialRight)

open QAlgorithms.Papers.Independent.Frontier18.P14 (occupationOutput)

open QAlgorithms.Papers.Independent.Gap48.P26 (thermalKernel)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.4--5, (18)--(19): a Gaussian density with M-I positive semidefinite
has a positive Gaussian coherent-product representation and is separable.
Printed: a positive Gaussian function. Changed: a Gaussian probability measure.
Why: M=I is the vacuum Dirac law; singular M-I requires delta factors. This
forced boundary correction requires independent moderation. The Fourier argument
uses only M-I>=0, not the undefined prescribed gain or standard-II ratios. -/
theorem positive_gaussian_p_representation
    (rho : State (FockIndex 2)) (M : Cov 2)
    (hgauss : GaussianWithCovariance rho.coefficients M) (hclassical : (M - 1).PosSemidef) :
    ∃ (mean : (Fin 2 × Fin 2) → ℝ) (mu : Measure ((Fin 2 × Fin 2) → ℝ))
      (ensemble : ((Fin 2 × Fin 2) → ℝ) → State (FockIndex 2)),
      (∀ v, CharacteristicSummable rho.coefficients v ∧
        multimodeWeylTrace rho.coefficients v = covarianceCharacteristicValue M mean v) ∧
      GaussianShiftLaw mu mean (M - 1) ∧ Measurable ensemble ∧
      (∀ x, (ensemble x).coefficients = coherentProductKernel x) ∧
      IsBarycenter mu (fun x => (ensemble x).coefficients) rho.coefficients ∧
      IsSeparable (pairedKernel rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
