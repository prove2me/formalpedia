-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:52:09.700188+00:00
-- url     : https://prove2.me/theorems/8598e4f7-0978-47b8-842a-0ed030fd4fc7
-- title:
--   Tanner Lifted Product: coeff rational Triangular Theta Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff rational Triangular Theta Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L73-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L73-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries (n : ℕ) :
    PowerSeries.coeff n rationalTriangularThetaSeries =
      (integerTriangularRoots n).card / 2 := by sorry
