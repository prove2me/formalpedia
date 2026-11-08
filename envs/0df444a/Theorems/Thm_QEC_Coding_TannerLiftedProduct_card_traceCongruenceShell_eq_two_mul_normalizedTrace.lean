-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_normalizedTrace
-- name    : QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_normalizedTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:34:46.224921+00:00
-- url     : https://prove2.me/theorems/f9b73dc2-5eec-47c7-8d50-0a658f7c3df3
-- title:
--   Tanner Lifted Product: card trace Congruence Shell eq two mul normalized Trace
-- statement:
--   Exact factor-two cardinality between the full trace shell and its
--   normalized positive-real-coordinate part.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L363-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L363-L369

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_normalizedTrace
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * Fintype.card (LPSNormalizedTraceQuaternion a n) := by sorry
