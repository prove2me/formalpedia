-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncToJ_involution
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_involution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:34:22.974778+00:00
-- url     : https://prove2.me/theorems/fd04abfc-59b5-4b05-85f0-ea78e17ff8ba
-- title:
--   Tanner Lifted Product: lps Original Rat Func To J involution
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rat Func To J involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L36-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L36-L64

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncToJ_involution (f : RatFunc ℂ) :
    lpsOriginalRatFuncToJ (InverseAffinePlace.rationalInvolution ℂ f) =
      lpsOriginalComplexJFractionInversion (lpsOriginalRatFuncToJ f) := by sorry
