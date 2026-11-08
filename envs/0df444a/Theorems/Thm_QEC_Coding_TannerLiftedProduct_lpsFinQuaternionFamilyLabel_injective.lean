-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFinQuaternionFamilyLabel_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsFinQuaternionFamilyLabel_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:58:42.569553+00:00
-- url     : https://prove2.me/theorems/4279cd58-9aaf-459a-b55d-5bbec6772054
-- title:
--   Tanner Lifted Product: lps Fin Quaternion Family Label injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Fin Quaternion Family Label injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L171-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSFamily.lean#L171-L176

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsFinQuaternionFamilyLabel_injective
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hCount : (lpsQuaternionShell p).card = p + 1) (n : ℕ) :
    Function.Injective (lpsFinQuaternionFamilyLabel hp hp4 hCount n) := by sorry
