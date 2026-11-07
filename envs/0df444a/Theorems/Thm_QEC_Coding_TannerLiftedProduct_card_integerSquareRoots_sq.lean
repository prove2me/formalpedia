-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_integerSquareRoots_sq
-- name    : QEC.Coding.TannerLiftedProduct.card_integerSquareRoots_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:43.741453+00:00
-- url     : https://prove2.me/theorems/824d774b-59b0-41d8-9984-39370aff9209
-- title:
--   Tanner Lifted Product: card integer Square Roots sq
-- statement:
--   Consequently every positive square contributes coefficient two to the
--   integer theta series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L59-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L59-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.card_integerSquareRoots_sq (m : ℕ) (hm : 0 < m) :
    (integerSquareRoots (m ^ 2)).card = 2 := by sorry
