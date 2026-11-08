-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:44.098921+00:00
-- url     : https://prove2.me/theorems/e9c6b343-0fa5-42ca-9b46-b4c873745b9c
-- title:
--   Tanner Lifted Product: lps Quaternion Word Product cons
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Word Product cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L78-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L78-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
    (t : LPSGeneratorIndex p) (word : List (LPSGeneratorIndex p)) :
    lpsQuaternionWordProduct (t :: word) =
      t.1 * lpsQuaternionWordProduct word := by sorry
