-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperProfile3_integral
-- name    : Sqrt6KissingBound.upperProfile3_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:15:24.498442+00:00
-- url     : https://prove2.me/theorems/8cf9623f-357f-4326-ae4e-cd1a6d508a32
-- title:
--   Sqrt6 Kissing Bound: upper Profile3 integral
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Profile3 integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L80-L96
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L80-L96

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.upperProfile3_integral :
    (∫ t in a_d3..1, upperProfile3 t ^ 2) = (2 : ℝ) / 3 - 3 * s3_d3 / 8 := by sorry
