-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionMatrix_conj
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:32:57.913031+00:00
-- url     : https://prove2.me/theorems/7ed02fd8-c056-40cc-a372-9d6d48dadf55
-- title:
--   Tanner Lifted Product: lps Quaternion Matrix conj
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Matrix conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L99-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L99-L104

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_conj
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t.conj = (lpsQuaternionMatrix q t).adjugate := by sorry
