-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsPSLWordProduct
-- name    : QEC.Coding.TannerLiftedProduct.toPGL_lpsPSLWordProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:11.676948+00:00
-- url     : https://prove2.me/theorems/035016c1-2361-4ae4-83ef-beb4ad468f58
-- title:
--   Tanner Lifted Product: to PGL lps PSLWord Product
-- statement:
--   The concrete `PSL` word maps to its multiplicative quaternion reduction
--   in `PGL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L143-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L143-L154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.toPGL_lpsPSLWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsPSLWordProduct a word) =
      lpsQuaternionAwayPGL a.q (lpsQuaternionAwayWordProduct a word) := by sorry
