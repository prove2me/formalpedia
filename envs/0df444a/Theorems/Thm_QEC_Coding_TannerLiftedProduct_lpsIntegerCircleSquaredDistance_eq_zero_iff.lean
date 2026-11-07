-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleSquaredDistance_eq_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:29.253237+00:00
-- url     : https://prove2.me/theorems/6580ff86-33ca-49d5-afd7-f6c2ac6c63ad
-- title:
--   Tanner Lifted Product: lps Integer Circle Squared Distance eq zero iff
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Circle Squared Distance eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L49-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L49-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_eq_zero_iff (a b : ℤ × ℤ) :
    lpsIntegerCircleSquaredDistance a b = 0 ↔ a = b := by sorry
