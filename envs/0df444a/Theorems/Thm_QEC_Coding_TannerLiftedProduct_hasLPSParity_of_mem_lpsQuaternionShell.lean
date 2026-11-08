-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_of_mem_lpsQuaternionShell
-- name    : QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:45:58.136468+00:00
-- url     : https://prove2.me/theorems/77747fe8-70d4-44c5-bf64-c3a8865eb2a2
-- title:
--   Tanner Lifted Product: has LPSParity of mem lps Quaternion Shell
-- statement:
--   A normalized norm-`p` LPS generator has the multiplicative parity class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L53-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L53-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasLPSParity_of_mem_lpsQuaternionShell
    (a : LPSResiduePrime p) {t : LPSQuaternion}
    (ht : t ∈ lpsQuaternionShell p) : t.HasLPSParity := by sorry
