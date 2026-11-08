-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22DistanceCoefficient_le_localWidth
-- name    : QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le_localWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:47.460107+00:00
-- url     : https://prove2.me/theorems/b5d3acd5-27ef-447a-899a-ea653ab2bc43
-- title:
--   Tanner Lifted Product: pk22 Distance Coefficient le local Width
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Distance Coefficient le local Width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L127-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L127-L139

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le_localWidth
    (q t : Nat) (_hq : 2 ≤ q) (hLarge : 23 ≤ q ^ t) :
    pk22DistanceCoefficient q t ≤ pk22LocalWidth q t := by sorry
