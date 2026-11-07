-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalBivariateFraction_taylor_equation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateFraction_taylor_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:23:06.210582+00:00
-- url     : https://prove2.me/theorems/efad81d4-275c-4a53-bac1-5ca2a6669077
-- title:
--   Tanner Lifted Product: lps Original Bivariate Fraction taylor equation
-- statement:
--   Global original polynomial fraction identity produces its real cusp Taylor equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L580-L640
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L580-L640

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateFraction_taylor_equation
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (G H : Polynomial (Polynomial ℂ)) (B : ℕ)
    (hG : lpsOriginalClearingBound M G ≤ B)
    (hH : lpsOriginalClearingBound M H ≤ B)
    (he : lpsOriginalJNHolomorphic N hN *
        lpsOriginalBivariateHolomorphicEval M hM H =
      lpsOriginalBivariateHolomorphicEval M hM G) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.X ^ N) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B G) =
      PowerSeries.map (algebraMap ℚ ℂ)
          (PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B H) := by sorry
