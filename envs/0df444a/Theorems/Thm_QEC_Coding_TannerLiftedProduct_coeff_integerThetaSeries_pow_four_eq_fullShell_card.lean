-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_pow_four_eq_fullShell_card
-- name    : QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_fullShell_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:43.769361+00:00
-- url     : https://prove2.me/theorems/56e83cf2-9e61-4851-b0aa-cb789645c616
-- title:
--   Tanner Lifted Product: coeff integer Theta Series pow four eq full Shell card
-- statement:
--   The full ordered signed representation count is exactly the coefficient
--   of the fourth power of the integer theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L216-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L216-L226

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_fullShell_card
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      (lpsQuaternionFullShell n).card := by sorry
