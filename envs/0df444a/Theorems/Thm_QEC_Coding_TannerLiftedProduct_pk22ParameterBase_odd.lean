-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_odd
-- name    : QEC.Coding.TannerLiftedProduct.pk22ParameterBase_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:12.847289+00:00
-- url     : https://prove2.me/theorems/ebe93d98-b5ed-40b7-b5a0-1f5b604d2160
-- title:
--   Tanner Lifted Product: pk22 Parameter Base odd
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Parameter Base odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L41-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L41-L43

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22ParameterBase_odd (q t : Nat) :
    Odd (pk22ParameterBase q t) := by sorry
