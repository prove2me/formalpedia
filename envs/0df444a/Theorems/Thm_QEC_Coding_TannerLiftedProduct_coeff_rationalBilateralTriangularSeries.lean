-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
-- name    : QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:51:58.891076+00:00
-- url     : https://prove2.me/theorems/36e0478e-a895-4773-ae85-ec18403ca5dd
-- title:
--   Tanner Lifted Product: coeff rational Bilateral Triangular Series
-- statement:
--   The Tanner Lifted Product construction uses the coeff rational Bilateral Triangular Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L58-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiThetaSeries.lean#L58-L61

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries (n : ℕ) :
    PowerSeries.coeff n rationalBilateralTriangularSeries =
      (integerTriangularRoots n).card := by sorry
