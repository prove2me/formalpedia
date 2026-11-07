-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsEffectiveQuaternionPSL
-- name    : QEC.Coding.TannerLiftedProduct.toPGL_lpsEffectiveQuaternionPSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:43.807277+00:00
-- url     : https://prove2.me/theorems/6ae753d5-5286-4631-b70b-2c12d5d12d23
-- title:
--   Tanner Lifted Product: to PGL lps Effective Quaternion PSL
-- statement:
--   The Tanner Lifted Product construction uses the to PGL lps Effective Quaternion PSL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L68-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L68-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.toPGL_lpsEffectiveQuaternionPSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (lpsEffectiveQuaternionPSL a t ht) =
      lpsQuaternionPGL a t ht := by sorry
