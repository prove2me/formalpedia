-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_append
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:48:36.09399+00:00
-- url     : https://prove2.me/theorems/99ab37c2-596c-4061-b769-8eaba009a1c2
-- title:
--   Tanner Lifted Product: lps Quaternion Word Product append
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Word Product append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L51-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L51-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_append
    (word₁ word₂ : List (LPSGeneratorIndex p)) :
    lpsQuaternionWordProduct (word₁ ++ word₂) =
      lpsQuaternionWordProduct word₁ * lpsQuaternionWordProduct word₂ := by sorry
