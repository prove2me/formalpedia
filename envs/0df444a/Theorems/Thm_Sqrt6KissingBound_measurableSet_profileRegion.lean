-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_profileRegion
-- name    : Sqrt6KissingBound.measurableSet_profileRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:01.891191+00:00
-- url     : https://prove2.me/theorems/daf6d797-85e9-4e50-91a1-566cd68bf27a
-- title:
--   Sqrt6 Kissing Bound: measurable Set profile Region
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set profile Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L39-L55
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L39-L55

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.measurableSet_profileRegion (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (profileRegion d s g) := by sorry
