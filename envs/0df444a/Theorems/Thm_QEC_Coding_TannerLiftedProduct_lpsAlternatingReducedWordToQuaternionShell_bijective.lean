-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_bijective
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:01:46.757328+00:00
-- url     : https://prove2.me/theorems/67b1aeba-23cb-4e3f-98be-cc3510cd8409
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word To Quaternion Shell bijective
-- statement:
--   The explicit alternating normal-form map is a bijection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L294-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L294-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_bijective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Bijective
      (lpsAlternatingReducedWordToQuaternionShell a n) := by sorry
