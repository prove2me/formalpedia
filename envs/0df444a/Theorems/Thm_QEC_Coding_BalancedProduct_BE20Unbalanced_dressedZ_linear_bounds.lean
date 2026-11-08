-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dressedZ_linear_bounds
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.dressedZ_linear_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:56.101974+00:00
-- url     : https://prove2.me/theorems/653a4e97-1be1-4238-b878-b9e2e02538e3
-- title:
--   BE20 Unbalanced: dressed Z linear bounds
-- statement:
--   The BE20 Unbalanced construction uses the dressed Z linear bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L232-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L232-L290

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.dressedZ_linear_bounds
    (q N : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hN : N = 401 * q * (q ^ 2 - 1)) :
    N ≤ dressedZCoefficient * lpsDressedZLowerBound q hq ∧
      lpsDressedZLowerBound q hq ≤ N := by sorry
