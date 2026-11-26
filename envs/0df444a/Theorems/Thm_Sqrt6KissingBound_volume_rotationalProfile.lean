-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volume_rotationalProfile
-- name    : Sqrt6KissingBound.volume_rotationalProfile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:04:23.243357+00:00
-- url     : https://prove2.me/theorems/23c17b07-a9fa-5170-9992-83cc3ef7a8c8
-- title:
--   Sqrt6 Kissing Bound: volume rotational Profile
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume rotational Profile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L88-L99
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L88-L99

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.volume_rotationalProfile (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
        (rotationalProfile d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by sorry
