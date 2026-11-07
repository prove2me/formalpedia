-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsQuaternionPSL
-- name    : QEC.Coding.TannerLiftedProduct.toPGL_lpsQuaternionPSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:00.84796+00:00
-- url     : https://prove2.me/theorems/284848a6-800b-47cd-805e-76424516a4cb
-- title:
--   Tanner Lifted Product: to PGL lps Quaternion PSL
-- statement:
--   The Tanner Lifted Product construction uses the to PGL lps Quaternion PSL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L173-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternion.lean#L173-L178

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

theorem QEC.Coding.TannerLiftedProduct.toPGL_lpsQuaternionPSL
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionPSL a t ht) = lpsQuaternionPGL a t ht := by sorry
