-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquareAbs_fiber_card_le_eight
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareAbs_fiber_card_le_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:23.30423+00:00
-- url     : https://prove2.me/theorems/1bfc3b4a-3e0f-4763-ad79-8b4f60c339c2
-- title:
--   Tanner Lifted Product: lps Integer Three Square Abs fiber card le eight
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Three Square Abs fiber card le eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L369-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L369-L383

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareAbs_fiber_card_le_eight
    (s : Finset ((ℤ × ℤ) × ℤ)) (a : (ℕ × ℕ) × ℕ) :
    (s.filter fun b => lpsIntegerThreeSquareAbs b=a).card ≤ 8 := by sorry
