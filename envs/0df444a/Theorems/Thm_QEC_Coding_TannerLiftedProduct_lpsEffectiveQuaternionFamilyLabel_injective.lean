-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionFamilyLabel_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:47:35.047605+00:00
-- url     : https://prove2.me/theorems/971a356d-61ac-48b6-b921-ac309e67523d
-- title:
--   Tanner Lifted Product: lps Effective Quaternion Family Label injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Quaternion Family Label injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L126-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectivePrime.lean#L126-L130

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionFamilyLabel_injective {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Function.Injective (lpsEffectiveQuaternionFamilyLabel hp hp4 n) := by sorry
