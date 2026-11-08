-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
-- name    : QEC.Coding.TannerLiftedProduct.lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:46:50.096819+00:00
-- url     : https://prove2.me/theorems/856995d8-3064-466d-ace9-14fb37151354
-- title:
--   Tanner Lifted Product: lps PSLWord Product eq one iff mem trace Congruence Shell
-- statement:
--   A finite LPS word closes at the identity exactly when its integral
--   quaternion product belongs to the trace congruence shell at norm `p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L193-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionWord.lean#L193-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
    (a : LPSResiduePrime p) (word : List (LPSGeneratorIndex p)) :
    lpsPSLWordProduct a word = 1 ↔
      lpsQuaternionWordProduct word ∈
        lpsTraceCongruenceShell a.q (p ^ word.length) := by sorry
