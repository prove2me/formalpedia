-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upper_point_mem_cone_ball
-- name    : Sqrt6KissingBound.upper_point_mem_cone_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:05:30.912836+00:00
-- url     : https://prove2.me/theorems/82054e77-7776-5750-8441-421aeedb29fd
-- title:
--   Sqrt6 Kissing Bound: upper point mem cone ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper point mem cone ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L81-L122
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L81-L122

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.upper_point_mem_cone_ball (k : ℕ) {t : ℝ} {v : Fin (k + 1) → ℝ}
    (hta : a_bg < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ <
      upperSlope_bg * (1 - t)) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by sorry
