-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_six_mul_cube
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_six_mul_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:07.786211+00:00
-- url     : https://prove2.me/theorems/07649a7c-9951-4161-9de7-b527a54609cf
-- title:
--   Tanner Lifted Product: lps Nat Circle card le six mul cube
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle card le six mul cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L284-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L284-L307

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_six_mul_cube (s : Finset (ℕ × ℕ)) (n K : ℕ)
    (hK : 0 < K) (hn : n ≤ K^8) (hs : ∀ a ∈ s, a.1^2+a.2^2=n) :
    s.card ≤ 6*K^3 := by sorry
