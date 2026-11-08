-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_lpsQuaternionWordProduct
-- name    : QEC.Coding.TannerLiftedProduct.hasLPSParity_lpsQuaternionWordProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:24.758577+00:00
-- url     : https://prove2.me/theorems/6aad5190-7bf6-469e-9eb6-58161c71ddc7
-- title:
--   Tanner Lifted Product: has LPSParity lps Quaternion Word Product
-- statement:
--   Every word in normalized LPS generators stays in the LPS parity class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L85-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L85-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasLPSParity_lpsQuaternionWordProduct
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    (lpsQuaternionWordProduct word).HasLPSParity := by sorry
