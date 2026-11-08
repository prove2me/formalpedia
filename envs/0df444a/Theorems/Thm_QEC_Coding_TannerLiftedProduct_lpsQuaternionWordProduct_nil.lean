-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:34.466302+00:00
-- url     : https://prove2.me/theorems/d8bd3b54-ed9f-4848-ac4b-8136480e8891
-- title:
--   Tanner Lifted Product: lps Quaternion Word Product nil
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Word Product nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L75-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L75-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil :
    lpsQuaternionWordProduct ([] : List (LPSGeneratorIndex p)) = 1 := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
