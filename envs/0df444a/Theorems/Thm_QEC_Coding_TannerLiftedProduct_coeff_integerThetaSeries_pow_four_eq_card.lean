-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_pow_four_eq_card
-- name    : QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:40.187509+00:00
-- url     : https://prove2.me/theorems/9cb7b9ec-18df-480b-a9ec-ea85e58b25a2
-- title:
--   Tanner Lifted Product: coeff integer Theta Series pow four eq card
-- statement:
--   The fourth theta coefficient counts the explicit exponent/root
--   witnesses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L126-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L126-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_card (n : ℕ) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      Fintype.card (IntegerThetaFourWitness n) := by sorry
