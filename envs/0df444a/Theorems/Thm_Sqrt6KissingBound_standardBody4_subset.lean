-- Prove2me | Theorems.Thm_Sqrt6KissingBound_standardBody4_subset
-- name    : Sqrt6KissingBound.standardBody4_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:00.685369+00:00
-- url     : https://prove2.me/theorems/28859135-bf8d-4f47-acd2-2153fed25ff1
-- title:
--   Sqrt6 Kissing Bound: standard Body4 subset
-- statement:
--   The Sqrt6 Kissing Bound construction uses the standard Body4 subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L113-L114
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L113-L114

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.standardBody4_subset : standardBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 := by sorry
