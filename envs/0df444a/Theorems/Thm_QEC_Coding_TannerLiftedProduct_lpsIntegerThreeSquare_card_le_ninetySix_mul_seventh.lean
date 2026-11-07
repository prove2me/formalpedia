-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:50:14.930205+00:00
-- url     : https://prove2.me/theorems/bee5e027-ca11-4663-ba89-3e6d8e437b3d
-- title:
--   Tanner Lifted Product: lps Integer Three Square card le ninety Six mul seventh
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Three Square card le ninety Six mul seventh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L385-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L385-L401

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
    (s : Finset ((ℤ × ℤ) × ℤ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^8)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=(n : ℤ)) : s.card ≤ 96*K^7 := by sorry
