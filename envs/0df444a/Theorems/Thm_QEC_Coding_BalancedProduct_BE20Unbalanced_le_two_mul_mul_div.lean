-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_le_two_mul_mul_div
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.le_two_mul_mul_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:32.933204+00:00
-- url     : https://prove2.me/theorems/53017ca1-4c6b-4dc4-9f47-9b1331b18afc
-- title:
--   BE20 Unbalanced: le two mul mul div
-- statement:
--   A quotient loses at most a factor two once its denominator fits in its
--   numerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L27-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L27-L39

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.le_two_mul_mul_div
    (a d : Nat) (hd : 0 < d) (hda : d ≤ a) :
    a ≤ 2 * d * (a / d) := by sorry
