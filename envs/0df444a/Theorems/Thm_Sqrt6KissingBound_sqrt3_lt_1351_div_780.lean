-- Prove2me | Theorems.Thm_Sqrt6KissingBound_sqrt3_lt_1351_div_780
-- name    : Sqrt6KissingBound.sqrt3_lt_1351_div_780
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:16:46.256853+00:00
-- url     : https://prove2.me/theorems/61e7eb12-c8fd-5765-9a3f-63b1f42a46b0
-- title:
--   Sqrt6 Kissing Bound: sqrt3 lt 1351 div 780
-- statement:
--   The Sqrt6 Kissing Bound construction uses the sqrt3 lt 1351 div 780 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L172-L177
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L172-L177

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.sqrt3_lt_1351_div_780 : s3_d4 < (1351 : ℝ) / 780 := by sorry
