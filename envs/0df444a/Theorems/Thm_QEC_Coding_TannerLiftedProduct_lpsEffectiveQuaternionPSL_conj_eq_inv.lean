-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_conj_eq_inv
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_conj_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:54:53.52148+00:00
-- url     : https://prove2.me/theorems/fb0992e9-4961-4033-a906-43595d063fcb
-- title:
--   Tanner Lifted Product: lps Effective Quaternion PSL conj eq inv
-- statement:
--   The computed projective label respects quaternion conjugate inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L90-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L90-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_conj_eq_inv (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t.conj (by simpa using ht) =
      (lpsEffectiveQuaternionPSL a t ht)⁻¹ := by sorry
