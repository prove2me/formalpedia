-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_mul_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:17.35719+00:00
-- url     : https://prove2.me/theorems/9ac1e6d0-5348-47fd-9d11-48af9d464239
-- title:
--   Tanner Lifted Product: lps Original Rational Series Retraction mul map
-- statement:
--   Q-linearity commutes with genuine rational-series convolution, not arbitrary products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L31-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L31-L42

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_mul_map
    (S : PowerSeries ℂ) (T : PowerSeries ℚ) :
    lpsOriginalRationalSeriesRetraction
      (S * PowerSeries.map (algebraMap ℚ ℂ) T) =
        lpsOriginalRationalSeriesRetraction S * T := by sorry
