-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_lpsQuaternionLabel_eq_inv
-- name    : QEC.Coding.TannerLiftedProduct.exists_lpsQuaternionLabel_eq_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:58:01.511129+00:00
-- url     : https://prove2.me/theorems/7391d89f-1071-4e1f-a405-c412ec1a9d45
-- title:
--   Tanner Lifted Product: exists lps Quaternion Label eq inv
-- statement:
--   Quaternion conjugation supplies the inverse-labelled direction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L87-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L87-L97

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.exists_lpsQuaternionLabel_eq_inv
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    ∃ u : LPSGeneratorIndex p,
      lpsQuaternionLabel a u = (lpsQuaternionLabel a t)⁻¹ := by sorry
