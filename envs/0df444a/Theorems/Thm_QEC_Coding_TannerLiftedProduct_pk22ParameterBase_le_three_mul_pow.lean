-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_le_three_mul_pow
-- name    : QEC.Coding.TannerLiftedProduct.pk22ParameterBase_le_three_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:16:01.516256+00:00
-- url     : https://prove2.me/theorems/5e2514a0-0cd7-49fe-a810-1481e798b84c
-- title:
--   Tanner Lifted Product: pk22 Parameter Base le three mul pow
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Parameter Base le three mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L54-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L54-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22ParameterBase_le_three_mul_pow
    (q t : Nat) (hq : 0 < q) :
    pk22ParameterBase q t ≤ 3 * q ^ t := by sorry
