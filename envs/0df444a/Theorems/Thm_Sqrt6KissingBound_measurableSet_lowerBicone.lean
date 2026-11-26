-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_lowerBicone
-- name    : Sqrt6KissingBound.measurableSet_lowerBicone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:06:26.826902+00:00
-- url     : https://prove2.me/theorems/2ac288b6-c3b5-5834-903a-6f7ee9f5a7b2
-- title:
--   Sqrt6 Kissing Bound: measurable Set lower Bicone
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set lower Bicone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L72-L74
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L72-L74

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.measurableSet_lowerBicone (k : ℕ) : MeasurableSet (lowerBicone k) := by sorry
