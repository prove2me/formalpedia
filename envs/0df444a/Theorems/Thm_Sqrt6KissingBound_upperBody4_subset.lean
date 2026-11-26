-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperBody4_subset
-- name    : Sqrt6KissingBound.upperBody4_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:10:57.621862+00:00
-- url     : https://prove2.me/theorems/582722d7-2953-4c4f-b160-1fa8c1e6c7ec
-- title:
--   Sqrt6 Kissing Bound: upper Body4 subset
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Body4 subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L105-L111
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L105-L111

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.upperBody4_subset : upperBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 := by sorry
