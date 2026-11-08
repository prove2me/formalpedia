-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquare_card_le_eightHundred_mul_fifth
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquare_card_le_eightHundred_mul_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:10.611619+00:00
-- url     : https://prove2.me/theorems/bf897a35-9938-4592-9676-ef70d51f4f89
-- title:
--   Tanner Lifted Product: lps Integer Three Square card le eight Hundred mul fifth
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Three Square card le eight Hundred mul fifth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L118-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L118-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquare_card_le_eightHundred_mul_fifth
    (s : Finset ((ℤ × ℤ) × ℤ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^6)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=(n : ℤ)) : s.card ≤ 800*K^5 := by sorry
