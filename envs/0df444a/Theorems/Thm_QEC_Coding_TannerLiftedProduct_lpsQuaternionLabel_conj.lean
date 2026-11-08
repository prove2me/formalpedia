-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:40:58.159837+00:00
-- url     : https://prove2.me/theorems/b2f106c0-0a9c-4913-9b53-53973d509c5d
-- title:
--   Tanner Lifted Product: lps Quaternion Label conj
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Label conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L99-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L99-L105

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    lpsQuaternionLabel a (lpsGeneratorConjEquiv a.degreePrime.pos t) =
      (lpsQuaternionLabel a t)⁻¹ := by sorry
