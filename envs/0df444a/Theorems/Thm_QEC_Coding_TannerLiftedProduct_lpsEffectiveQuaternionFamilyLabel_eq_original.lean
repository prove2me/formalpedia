-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_eq_original
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:48:09.621898+00:00
-- url     : https://prove2.me/theorems/076b9678-3e41-4e31-afad-18e890e5a2af
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Label eq original
-- statement:
--   The computed normalized labels are the semantic labels of the original family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L158-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L158-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_eq_original {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsEffectiveQuaternionFamilyLabel hp hp4 n = lpsQuaternionFamilyLabel hp hp4 n := by sorry
