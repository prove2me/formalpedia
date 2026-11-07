-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquareSignedBox_card_le_eight
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareSignedBox_card_le_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:20.331211+00:00
-- url     : https://prove2.me/theorems/4349d237-3c04-453e-9fc0-10ff8e2df3dd
-- title:
--   Tanner Lifted Product: lps Integer Three Square Signed Box card le eight
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Three Square Signed Box card le eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L360-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L360-L367

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareSignedBox_card_le_eight (a : (ℕ × ℕ) × ℕ) :
    (lpsIntegerThreeSquareSignedBox a).card ≤ 8 := by sorry
