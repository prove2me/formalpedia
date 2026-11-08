-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionAwayPGL_wordProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_wordProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:29.728121+00:00
-- url     : https://prove2.me/theorems/c8a1469a-1d3b-4723-97b5-51690eadb6fd
-- title:
--   Tanner Lifted Product: lps Quaternion Away PGL word Product
-- statement:
--   Projective reduction of a quaternion word is the product of the finite
--   LPS Hecke labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L124-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L124-L133

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionAwayPGL_wordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    lpsQuaternionAwayPGL a.q (lpsQuaternionAwayWordProduct a word) =
      (word.map (lpsPGLHeckeLabel a)).prod := by sorry
