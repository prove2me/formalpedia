-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_scale_bounds
-- name    : QEC.Coding.TannerLiftedProduct.pk22_scale_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:15.071988+00:00
-- url     : https://prove2.me/theorems/20d3c4c9-f3c6-4add-baef-f03a778fbb3a
-- title:
--   Tanner Lifted Product: pk22 scale bounds
-- statement:
--   The Tanner Lifted Product construction uses the pk22 scale bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L287-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalParameterSelection.lean#L287-L390

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.pk22_scale_bounds
    (q t x : Nat) (hx : pk22ScaleThreshold q t ≤ x) :
    0 < x ∧
    12 * 1 ≤ pk22DistanceCoefficient q t * x ^ 2 ∧
    12 * 1 + 6 ≤ pk22DistanceCoefficient q t * x ^ 2 ∧
    4 * pk22FaceCoefficient q t ≤
      1 * pk22DistanceCoefficient q t * x ^ 3 ∧
    2 * 1 + pk22SpectralCoefficient q t ≤
      pk22DistanceCoefficient q t * x ^ 2 ∧
    4 * pk22SpectralCoefficient q t ≤ 1 * x ∧
    16 * (128 * pk22LocalWidth q t + 6 * x + 1) *
        (pk22SpectralCoefficient q t) ^ 2 ≤
      pk22FaceCoefficient q t * x ∧
    pk22RectangleConstant q t <
      1 * pk22RowCoefficient q t * x := by sorry
