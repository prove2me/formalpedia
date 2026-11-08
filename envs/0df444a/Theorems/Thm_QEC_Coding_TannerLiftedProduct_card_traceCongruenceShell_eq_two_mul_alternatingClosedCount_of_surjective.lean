-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
-- name    : QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:36:41.020052+00:00
-- url     : https://prove2.me/theorems/6ca2a4a1-eafc-4d11-8452-b3bafb0e1d25
-- title:
--   Tanner Lifted Product: card trace Congruence Shell eq two mul alternating Closed Count of surjective
-- statement:
--   Conditional form of the exact LPS trace identity (4.14).  Its sole
--   remaining hypothesis is existence of the explicit integral quaternion
--   normal form; uniqueness has already been discharged by cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L466-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L466-L476

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_traceCongruenceShell_eq_two_mul_alternatingClosedCount_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    (lpsTraceCongruenceShell a.q (p ^ n)).card =
      2 * lpsAlternatingClosedReducedWordCount a n := by sorry
