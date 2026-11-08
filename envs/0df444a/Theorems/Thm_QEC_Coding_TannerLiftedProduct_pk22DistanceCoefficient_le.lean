-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22DistanceCoefficient_le
-- name    : QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:32.454283+00:00
-- url     : https://prove2.me/theorems/5d10e356-e6e0-466c-9348-9a73844f3369
-- title:
--   Tanner Lifted Product: pk22 Distance Coefficient le
-- statement:
--   The Tanner Lifted Product construction uses the pk22 Distance Coefficient le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L85-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L85-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le
    (q t : Nat) (hq : 2 ≤ q) :
    pk22DistanceCoefficient q t ≤ 4608 * q ^ (2 * t) := by sorry
