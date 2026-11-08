-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyIndex_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:18:17.54007+00:00
-- url     : https://prove2.me/theorems/7d4287b2-0a00-4ebb-81f9-d98805321b7c
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Index injective
-- statement:
--   Distinct actual directions receive distinct computed vertex indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L148-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L148-L155

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyIndex_injective {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsEffectiveQuaternionFamilyIndex hp hp4 n) := by sorry
