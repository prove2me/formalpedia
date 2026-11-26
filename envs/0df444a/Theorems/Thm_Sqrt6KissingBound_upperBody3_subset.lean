-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperBody3_subset
-- name    : Sqrt6KissingBound.upperBody3_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:09:37.286919+00:00
-- url     : https://prove2.me/theorems/b8ab50d4-6b7e-5191-913e-ee21ec1893fe
-- title:
--   Sqrt6 Kissing Bound: upper Body3 subset
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Body3 subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L64-L70
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L64-L70

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.upperBody3_subset : upperBody3 ⊆ strictCone (standardAxis 2) ∩ ball 0 1 := by sorry
