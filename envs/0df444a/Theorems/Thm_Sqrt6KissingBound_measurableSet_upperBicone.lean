-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBicone
-- name    : Sqrt6KissingBound.measurableSet_upperBicone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:08:09.340898+00:00
-- url     : https://prove2.me/theorems/0485f97f-3e86-4050-9ccf-36cca1d617f0
-- title:
--   Sqrt6 Kissing Bound: measurable Set upper Bicone
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set upper Bicone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L76-L78
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L76-L78

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

theorem Sqrt6KissingBound.measurableSet_upperBicone (k : ℕ) : MeasurableSet (upperBicone k) := by sorry
