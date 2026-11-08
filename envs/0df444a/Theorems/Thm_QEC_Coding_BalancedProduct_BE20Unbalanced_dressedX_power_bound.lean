-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dressedX_power_bound
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.dressedX_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:58.003136+00:00
-- url     : https://prove2.me/theorems/e686b81f-3051-4e7e-a5af-fd978afc6327
-- title:
--   BE20 Unbalanced: dressed X power bound
-- statement:
--   The BE20 Unbalanced construction uses the dressed X power bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L193-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L193-L230

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.dressedX_power_bound
    (q N : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hN : N = 401 * q * (q ^ 2 - 1)) :
    N ≤ dressedXCoefficient * lpsDressedXLowerBound q ^ 3 := by sorry
