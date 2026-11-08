-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:49:01.932855+00:00
-- url     : https://prove2.me/theorems/a515cfb2-4bc0-442b-bf20-7a0d5867c2f6
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word To Quaternion Shell surjective
-- statement:
--   The explicit alternating-normal-form map is surjective.  This is the
--   existence statement in the classical LPS quaternion factorization lemma.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L264-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L264-L291

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordToQuaternionShell_surjective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n) := by sorry
