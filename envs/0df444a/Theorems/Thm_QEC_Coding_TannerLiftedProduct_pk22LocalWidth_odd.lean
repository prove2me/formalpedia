-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22LocalWidth_odd
-- name    : QEC.Coding.TannerLiftedProduct.pk22LocalWidth_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:05.291936+00:00
-- url     : https://prove2.me/theorems/3b4b8af7-a42d-4927-bc12-18528e0fcd6f
-- title:
--   Tanner Lifted Product: pk22 Local Width odd
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Local Width odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L45-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L45-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22LocalWidth_odd (q t : Nat) :
    Odd (pk22LocalWidth q t) := by sorry
