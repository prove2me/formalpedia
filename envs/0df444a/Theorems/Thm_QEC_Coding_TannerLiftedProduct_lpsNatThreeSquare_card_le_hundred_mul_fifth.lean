-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatThreeSquare_card_le_hundred_mul_fifth
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatThreeSquare_card_le_hundred_mul_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:57:20.495199+00:00
-- url     : https://prove2.me/theorems/e0d26528-f384-4de3-8a18-fd56f83768ee
-- title:
--   Tanner Lifted Product: lps Nat Three Square card le hundred mul fifth
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Three Square card le hundred mul fifth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L85-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSAdaptiveThreeSquareCount.lean#L85-L116

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAdaptiveThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatThreeSquare_card_le_hundred_mul_fifth
    (s : Finset ((ℕ × ℕ) × ℕ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^6)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=n) : s.card ≤ 100*K^5 := by sorry
