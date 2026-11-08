-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_X
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:33:48.108985+00:00
-- url     : https://prove2.me/theorems/71446a98-c697-49d1-8928-a958de9ad39d
-- title:
--   Tanner Lifted Product: lps Original Rat Func To J X
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rat Func To J X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L31-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L31-L34

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_X :
    lpsOriginalRatFuncToJ RatFunc.X = algebraMap P J Polynomial.X := by sorry
