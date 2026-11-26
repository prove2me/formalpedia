-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volume_profileRegion
-- name    : Sqrt6KissingBound.volume_profileRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:22.067049+00:00
-- url     : https://prove2.me/theorems/a7a93558-a4fa-527f-b99c-2a8212949de3
-- title:
--   Sqrt6 Kissing Bound: volume profile Region
-- statement:
--   Fubini formula for a body with ball-shaped transverse sections.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L58-L75
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L58-L75

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.volume_profileRegion (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (ℝ × (Fin d → ℝ))) (profileRegion d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by sorry
