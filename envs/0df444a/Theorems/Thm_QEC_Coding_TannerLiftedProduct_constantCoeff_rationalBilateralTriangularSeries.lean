-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
-- name    : QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:03.592199+00:00
-- url     : https://prove2.me/theorems/b467dc85-d0c4-4176-a563-a0ff1d3ead26
-- title:
--   Tanner Lifted Product: constant Coeff rational Bilateral Triangular Series
-- statement:
--   The Tanner Lifted Product construction uses the constant Coeff rational Bilateral Triangular Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L63-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L63-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries :
    PowerSeries.constantCoeff rationalBilateralTriangularSeries = 2 := by sorry
