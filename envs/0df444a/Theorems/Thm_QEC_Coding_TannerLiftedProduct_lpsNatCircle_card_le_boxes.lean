-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_boxes
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_boxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:57.832326+00:00
-- url     : https://prove2.me/theorems/b44f76af-a663-44f4-8c3e-a0cdce4e1563
-- title:
--   Tanner Lifted Product: lps Nat Circle card le boxes
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Circle card le boxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L245-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L245-L257

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_boxes (s : Finset (ℕ × ℕ)) (n M L : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) : s.card ≤ 2*(2*M+1) := by sorry
