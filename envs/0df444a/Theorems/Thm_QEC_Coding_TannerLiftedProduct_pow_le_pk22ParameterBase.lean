-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_pk22ParameterBase
-- name    : QEC.Coding.TannerLiftedProduct.pow_le_pk22ParameterBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:14:57.974613+00:00
-- url     : https://prove2.me/theorems/366273d0-3796-4e52-a3a7-e124649c1ba1
-- title:
--   Tanner Lifted Product: pow le pk22 Parameter Base
-- statement:
--   The Tanner Lifted Product construction uses the pow le pk22 Parameter Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L49-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L49-L52

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pow_le_pk22ParameterBase (q t : Nat) :
    q ^ t ≤ pk22ParameterBase q t := by sorry
