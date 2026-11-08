-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dimension_power_bounds
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.dimension_power_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:29.278568+00:00
-- url     : https://prove2.me/theorems/a0ed14d0-6930-48a2-804b-fd7a63041f47
-- title:
--   BE20 Unbalanced: dimension power bounds
-- statement:
--   The BE20 Unbalanced construction uses the dimension power bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L125-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L125-L191

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.dimension_power_bounds
    (q N K : Nat)
    (hqLarge : familyThreshold ≤ q)
    (hN : N = 401 * q * (q ^ 2 - 1))
    (hKLower : q ^ 2 - 1 ≤ K)
    (hKUpper : K ≤ 201 * (q ^ 2 - 1)) :
    N ^ 2 ≤ dimensionLowerCoefficient * K ^ 3 ∧
      K ^ 3 ≤ dimensionUpperCoefficient * N ^ 2 := by sorry
