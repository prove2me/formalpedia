-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:32.231813+00:00
-- url     : https://prove2.me/theorems/a9491cc5-d990-4b38-949c-3d7f0772df28
-- title:
--   Tanner Lifted Product: lps Quaternion Label injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Label injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L53-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L53-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_injective (a : LPSResiduePrime p) :
    Function.Injective (lpsQuaternionLabel a) := by sorry
