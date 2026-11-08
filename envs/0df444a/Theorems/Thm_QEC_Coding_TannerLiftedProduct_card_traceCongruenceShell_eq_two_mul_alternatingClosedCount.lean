-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_alternatingClosedCount
-- name    : QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:48:44.304949+00:00
-- url     : https://prove2.me/theorems/e81be4d0-17bb-4748-af77-6eb4696c926a
-- title:
--   Tanner Lifted Product: card trace Congruence Shell eq two mul alternating Closed Count
-- statement:
--   Exact LPS formula (4.14): the trace-congruence quaternion count is
--   twice the alternating closed reduced-word count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L303-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L303-L308

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n := by sorry
