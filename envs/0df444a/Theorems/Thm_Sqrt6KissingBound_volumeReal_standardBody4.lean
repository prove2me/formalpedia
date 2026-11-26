-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volumeReal_standardBody4
-- name    : Sqrt6KissingBound.volumeReal_standardBody4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:15.423049+00:00
-- url     : https://prove2.me/theorems/c380d295-3aa5-4664-8135-cdfba63d9be3
-- title:
--   Sqrt6 Kissing Bound: volume Real standard Body4
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume Real standard Body4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L162-L170
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L162-L170

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.volumeReal_standardBody4 :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real standardBody4 =
      ((265352 - 153195 * s3_d4) / 320) * unitBallVolumeReal 3 := by sorry
