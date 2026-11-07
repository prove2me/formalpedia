-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_conj_eq_inv
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_conj_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:32:57.848702+00:00
-- url     : https://prove2.me/theorems/94e98ac4-1b9d-4c42-adb9-a1c582d3889d
-- title:
--   Tanner Lifted Product: lps Quaternion PSL conj eq inv
-- statement:
--   Quaternion conjugation gives inversion already in `PSL`, not merely
--   after embedding into `PGL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L217-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L217-L224

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_conj_eq_inv
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPSL a t.conj (by simpa using ht) =
      (lpsQuaternionPSL a t ht)⁻¹ := by sorry
