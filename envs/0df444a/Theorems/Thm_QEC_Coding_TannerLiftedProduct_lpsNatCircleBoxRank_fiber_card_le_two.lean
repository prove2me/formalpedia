-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircleBoxRank_fiber_card_le_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_fiber_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:48.060408+00:00
-- url     : https://prove2.me/theorems/fa43fd53-b95d-4dab-ba98-74819867395c
-- title:
--   Tanner Lifted Product: lps Nat Circle Box Rank fiber card le two
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle Box Rank fiber card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L209-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L209-L243

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_fiber_card_le_two (s : Finset (ℕ × ℕ)) (n M L j : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) :
    (s.filter fun a => lpsNatCircleBoxRank M L a = j).card ≤ 2 := by sorry
