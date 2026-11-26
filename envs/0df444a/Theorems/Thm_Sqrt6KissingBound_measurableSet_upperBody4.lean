-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBody4
-- name    : Sqrt6KissingBound.measurableSet_upperBody4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:10:49.544752+00:00
-- url     : https://prove2.me/theorems/d2bf4717-0be5-4b97-8a3f-864601b71ad3
-- title:
--   Sqrt6 Kissing Bound: measurable Set upper Body4
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set upper Body4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L72-L73
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L72-L73

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.measurableSet_upperBody4 : MeasurableSet upperBody4 := by sorry
