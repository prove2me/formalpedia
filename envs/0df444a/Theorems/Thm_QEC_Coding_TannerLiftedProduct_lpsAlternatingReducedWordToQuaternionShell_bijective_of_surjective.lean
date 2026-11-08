-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:04:14.034088+00:00
-- url     : https://prove2.me/theorems/f7c89e3a-2d09-45c7-84e8-9c6e259ed59f
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word To Quaternion Shell bijective of surjective
-- statement:
--   Once existence (surjectivity) of the classical quaternion factorization
--   is established, its uniqueness is automatic from the exact finite counts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L208-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean#L208-L214

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    Function.Bijective (lpsAlternatingReducedWordToQuaternionShell a n) := by sorry
