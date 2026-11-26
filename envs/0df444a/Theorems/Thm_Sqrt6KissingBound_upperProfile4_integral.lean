-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperProfile4_integral
-- name    : Sqrt6KissingBound.upperProfile4_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:16:21.317221+00:00
-- url     : https://prove2.me/theorems/fed72efb-ebfa-5523-823c-928453776b10
-- title:
--   Sqrt6 Kissing Bound: upper Profile4 integral
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Profile4 integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L124-L148
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L124-L148

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.upperProfile4_integral :
    (∫ t in a_d4..1, upperProfile4 t ^ 3) = (33169 - 19150 * s3_d4) / 40 := by sorry
