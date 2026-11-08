-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:36:23.626243+00:00
-- url     : https://prove2.me/theorems/d0b25cc0-6e76-4b38-af6d-6b5579f2abf2
-- title:
--   Tanner Lifted Product: lps Original Rat Func To J polynomial
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rat Func To J polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L27-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L27-L29

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_polynomial (p : P) :
    lpsOriginalRatFuncToJ (algebraMap P (RatFunc ℂ) p) = algebraMap P J p := by sorry
