-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsAlternatingReducedWord_eq_quaternionShell
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsAlternatingReducedWord_eq_quaternionShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:04:57.907908+00:00
-- url     : https://prove2.me/theorems/7a6ff926-540f-4a6f-af5f-2aa58aa46024
-- title:
--   Tanner Lifted Product: card lps Alternating Reduced Word eq quaternion Shell
-- statement:
--   Source and target of the finite normal-form map have equal cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L197-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L197-L204

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsAlternatingReducedWord_eq_quaternionShell
    (a : LPSResiduePrime p) (n : ℕ) :
    Fintype.card (LPSAlternatingReducedWord a.degreePrime.pos n) =
      Fintype.card {t // t ∈ lpsQuaternionShell (p ^ n)} := by sorry
