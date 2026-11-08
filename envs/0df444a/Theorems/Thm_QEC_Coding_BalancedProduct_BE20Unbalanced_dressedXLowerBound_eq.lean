-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dressedXLowerBound_eq
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.dressedXLowerBound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:43.145787+00:00
-- url     : https://prove2.me/theorems/58110e44-221e-401a-962a-cb54def677c7
-- title:
--   BE20 Unbalanced: dressed XLower Bound eq
-- statement:
--   The BE20 Unbalanced construction uses the dressed XLower Bound eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L99-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L99-L123

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.dressedXLowerBound_eq
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q) :
    lpsDressedXLowerBound q = (q / 804) / 37273 := by sorry
