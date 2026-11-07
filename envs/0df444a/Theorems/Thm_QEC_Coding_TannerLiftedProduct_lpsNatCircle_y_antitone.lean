-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_y_antitone
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircle_y_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:57.467717+00:00
-- url     : https://prove2.me/theorems/a9327d06-dac2-495f-a3be-aa15e0f34f9a
-- title:
--   Tanner Lifted Product: lps Nat Circle y antitone
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle y antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L181-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L181-L191

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircle_y_antitone (a b : ℕ × ℕ) (n : ℕ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hx : a.1 ≤ b.1) : b.2 ≤ a.2 := by sorry
