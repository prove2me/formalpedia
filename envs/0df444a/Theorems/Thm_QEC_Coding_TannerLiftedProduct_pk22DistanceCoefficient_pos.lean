-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22DistanceCoefficient_pos
-- name    : QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:45.886917+00:00
-- url     : https://prove2.me/theorems/005dcb46-b07a-410b-b8ff-1dc5cb69fa56
-- title:
--   Tanner Lifted Product: pk22 Distance Coefficient pos
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Distance Coefficient pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L276-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L276-L280

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_pos (q t : Nat) :
    0 < pk22DistanceCoefficient q t := by sorry
