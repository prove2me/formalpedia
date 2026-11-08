-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionFamilyLabel_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionFamilyLabel_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:41:25.980593+00:00
-- url     : https://prove2.me/theorems/a42505e7-ff0b-4c81-b229-77313f900774
-- title:
--   Tanner Lifted Product: lps Quaternion Family Label injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Quaternion Family Label injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L148-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L148-L151

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionFamilyLabel_injective
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsQuaternionFamilyLabel hp hp4 n) := by sorry
