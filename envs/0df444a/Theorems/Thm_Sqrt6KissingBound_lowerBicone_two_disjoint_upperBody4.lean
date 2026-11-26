-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lowerBicone_two_disjoint_upperBody4
-- name    : Sqrt6KissingBound.lowerBicone_two_disjoint_upperBody4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:16:09.585461+00:00
-- url     : https://prove2.me/theorems/f204f91f-c232-5239-8dd0-4444f76108ef
-- title:
--   Sqrt6 Kissing Bound: lower Bicone two disjoint upper Body4
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower Bicone two disjoint upper Body4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L116-L122
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L116-L122

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.lowerBicone_two_disjoint_upperBody4 : Disjoint (lowerBicone 2) upperBody4 := by sorry
