-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerSet_card_le_negativeRoot_class
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerSet_card_le_negativeRoot_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:50.540091+00:00
-- url     : https://prove2.me/theorems/bc2f8944-b097-41a0-b882-6f91a49609eb
-- title:
--   Tanner Lifted Product: lps Integer Set card le negative Root class
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Set card le negative Root class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L92-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L92-L117

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerSet_card_le_negativeRoot_class (s : Finset ℤ) (r M : ℕ)
    (hs : ∀ x ∈ s, -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ) ∧ (M : ℤ) ∣ x+(r : ℤ)) :
    s.card ≤ 2*r/M+1 := by sorry
