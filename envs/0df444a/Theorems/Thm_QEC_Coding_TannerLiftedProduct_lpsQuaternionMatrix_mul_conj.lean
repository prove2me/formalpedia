-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionMatrix_mul_conj
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:01.219675+00:00
-- url     : https://prove2.me/theorems/5b63995e-99e9-4a08-9ada-df406e4aa73a
-- title:
--   Tanner Lifted Product: lps Quaternion Matrix mul conj
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Matrix mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L117-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L117-L122

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

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_mul_conj
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t * lpsQuaternionMatrix q t.conj =
      (t.norm : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by sorry
