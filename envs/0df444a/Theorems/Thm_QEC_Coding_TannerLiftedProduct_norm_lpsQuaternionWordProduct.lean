-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionWordProduct
-- name    : QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionWordProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:02.922943+00:00
-- url     : https://prove2.me/theorems/d29617ed-82fe-498f-8fbc-75dd6df428b1
-- title:
--   Tanner Lifted Product: norm lps Quaternion Word Product
-- statement:
--   The norm of a length-`n` LPS generator word is `p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L95-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L95-L103

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    (lpsQuaternionWordProduct word).norm = (p : ℤ) ^ word.length := by sorry
