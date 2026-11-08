-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_singleton
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:50:05.726071+00:00
-- url     : https://prove2.me/theorems/f4b4638e-fc56-42c4-89ae-39154924a25e
-- title:
--   Tanner Lifted Product: lps Quaternion Word Product singleton
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Word Product singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L57-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_singleton
    (x : LPSGeneratorIndex p) :
    lpsQuaternionWordProduct [x] = x.1 := by sorry
