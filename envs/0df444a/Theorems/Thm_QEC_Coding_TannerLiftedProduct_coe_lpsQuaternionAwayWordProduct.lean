-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coe_lpsQuaternionAwayWordProduct
-- name    : QEC.Coding.TannerLiftedProduct.coe_lpsQuaternionAwayWordProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:42.021528+00:00
-- url     : https://prove2.me/theorems/2283590b-b041-4b5b-8202-55fa0b8941d8
-- title:
--   Tanner Lifted Product: coe lps Quaternion Away Word Product
-- statement:
--   The Tanner Lifted Product construction uses the coe lps Quaternion Away Word Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L112-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L112-L120

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coe_lpsQuaternionAwayWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    (lpsQuaternionAwayWordProduct a word : LPSQuaternion) =
      lpsQuaternionWordProduct word := by sorry
