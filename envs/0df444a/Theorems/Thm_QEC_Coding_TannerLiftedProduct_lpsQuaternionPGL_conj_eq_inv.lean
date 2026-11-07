-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPGL_conj_eq_inv
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_conj_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:32:56.109205+00:00
-- url     : https://prove2.me/theorems/3e28b2f6-e6b7-4340-985b-26e73169c51d
-- title:
--   Tanner Lifted Product: lps Quaternion PGL conj eq inv
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion PGL conj eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L180-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L180-L213

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

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_conj_eq_inv
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t.conj (by simpa using ht) =
      (lpsQuaternionPGL a t ht)⁻¹ := by sorry
