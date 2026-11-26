-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_rotationalProfile
-- name    : Sqrt6KissingBound.measurableSet_rotationalProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:33.446099+00:00
-- url     : https://prove2.me/theorems/388c115f-5a84-44ef-8ac8-003b47af76e8
-- title:
--   Sqrt6 Kissing Bound: measurable Set rotational Profile
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set rotational Profile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L82-L86
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L82-L86

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.measurableSet_rotationalProfile (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (rotationalProfile d s g) := by sorry
