-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_le_pow_add_two
-- name    : QEC.Coding.TannerLiftedProduct.pk22ParameterBase_le_pow_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:18.294717+00:00
-- url     : https://prove2.me/theorems/a6f43e14-4454-457b-a9ff-5f9c1ccd3de9
-- title:
--   Tanner Lifted Product: pk22 Parameter Base le pow add two
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Parameter Base le pow add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L61-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L61-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22ParameterBase_le_pow_add_two
    (q t : Nat) (hq : 2 ≤ q) :
    pk22ParameterBase q t ≤ q ^ (t + 2) := by sorry
