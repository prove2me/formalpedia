-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volumeReal_upperBody4
-- name    : Sqrt6KissingBound.volumeReal_upperBody4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:16:31.316175+00:00
-- url     : https://prove2.me/theorems/acddb157-013d-56e4-b5ba-33a18db2ba54
-- title:
--   Sqrt6 Kissing Bound: volume Real upper Body4
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume Real upper Body4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L150-L160
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L150-L160

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.volumeReal_upperBody4 :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real upperBody4 =
      ((33169 - 19150 * s3_d4) / 40) * unitBallVolumeReal 3 := by sorry
