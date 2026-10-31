-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P75_separable_epr_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P75.separable_epr_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:01:28.189196+00:00
-- url     : https://prove2.me/theorems/b5f06359-fe4e-48f9-8527-414e10a76fd0
-- title:
--   Theorem 1: separable EPR variance bound
-- statement:
--   Let $\rho$ be a normalized positive trace-class state of two completed oscillator modes. The dimensionless quadratures obey $[x_j,p_k]=i\delta_{jk}$, so vacuum quadrature variances are $1/2$. Assume that $\rho$ belongs to the trace-norm closed convex hull of product densities. For every nonzero real $a$, set $u=|a|x_1+x_2/a$ and $v=|a|p_1-p_2/a$. Then
--
--   $$
--   \operatorname{Var}_{\rho}(u)+\operatorname{Var}_{\rho}(v)\ge a^2+a^{-2}.
--   $$
--
--   Variances take values in $[0,+\infty]$; no Gaussian or finite-energy assumption is imposed. A violation certifies entanglement.
-- source:
--   Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, PDF p. 1, Theorem 1, Eqs. (2)–(3)

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

/-- Theorem 1, PDF pp.1--2, (2)--(3): every separable normalized two-mode
state obeys the extended-variance bound for every nonzero real gain. The state
may be non-Gaussian or have infinite energy or infinite quadrature variance. -/
theorem separable_epr_bound (rho : State (FockIndex 2)) (a : ℝ) (ha : a ≠ 0)
    (hsep : IsSeparable (pairedKernel rho.coefficients)) :
    ENNReal.ofReal (a ^ 2 + 1 / a ^ 2) ≤ eprTotalVariance rho.coefficients a := by sorry

end QAlgorithms.Papers.Independent.Intake100.P75

end
