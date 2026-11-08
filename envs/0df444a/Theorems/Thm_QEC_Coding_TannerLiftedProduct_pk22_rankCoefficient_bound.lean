-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_rankCoefficient_bound
-- name    : QEC.Coding.TannerLiftedProduct.pk22_rankCoefficient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:17.110258+00:00
-- url     : https://prove2.me/theorems/4da59ebb-a0c6-45d6-88e2-5f549b509e66
-- title:
--   Tanner Lifted Product: pk22 rank Coefficient bound
-- statement:
--   The Tanner Lifted Product construction uses the pk22 rank Coefficient bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L392-L401
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L392-L401

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22_rankCoefficient_bound (q t : Nat) :
    36 * 1 * pk22FaceCoefficient q t ≤
      5 * (pk22DistanceCoefficient q t) ^ 2 := by sorry
