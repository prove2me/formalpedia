-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_eq_ite
-- name    : QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:36:13.399227+00:00
-- url     : https://prove2.me/theorems/d2b17262-d1cf-4990-9987-b27df067104f
-- title:
--   Tanner Lifted Product: coeff integer Theta Series eq ite
-- statement:
--   Coefficientwise normal form of the integer theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L112-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L112-L115

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_eq_ite (n : ℕ) :
    PowerSeries.coeff n integerThetaSeries =
      if n = 0 then 1 else if IsSquare n then 2 else 0 := by sorry
