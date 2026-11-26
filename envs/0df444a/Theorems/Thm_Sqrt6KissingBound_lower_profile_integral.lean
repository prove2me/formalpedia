-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lower_profile_integral
-- name    : Sqrt6KissingBound.lower_profile_integral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:07:33.003881+00:00
-- url     : https://prove2.me/theorems/8d1983b4-cfc7-4fa6-b933-3c0a71976d6c
-- title:
--   Sqrt6 Kissing Bound: lower profile integral
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower profile integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L52-L56
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeVolume.lean#L52-L56

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

theorem Sqrt6KissingBound.lower_profile_integral (k : ℕ) :
    (∫ t in (0 : ℝ)..a_bv, (t / s3_bv) ^ (k + 1)) =
      s3_bv / ((k + 2) * 2 ^ (k + 2)) := by sorry
