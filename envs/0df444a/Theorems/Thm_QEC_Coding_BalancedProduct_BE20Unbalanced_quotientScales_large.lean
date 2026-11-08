-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_quotientScales_large
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.quotientScales_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:10.111566+00:00
-- url     : https://prove2.me/theorems/7da6ac5c-28ab-4907-abc9-1623a3b1a352
-- title:
--   BE20 Unbalanced: quotient Scales large
-- statement:
--   The BE20 Unbalanced construction uses the quotient Scales large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L78-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L78-L97

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.quotientScales_large
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1) :
    10000000 ≤ Fintype.card (EdgeOrbit401 q hq) ∧
      10000000 ≤ Fintype.card (CheckOrbit401 q) := by sorry
