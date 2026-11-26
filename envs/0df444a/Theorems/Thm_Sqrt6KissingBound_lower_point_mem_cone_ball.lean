-- Prove2me | Theorems.Thm_Sqrt6KissingBound_lower_point_mem_cone_ball
-- name    : Sqrt6KissingBound.lower_point_mem_cone_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:05:51.199541+00:00
-- url     : https://prove2.me/theorems/9f136019-905e-4f4c-a802-6aa9c9613dc7
-- title:
--   Sqrt6 Kissing Bound: lower point mem cone ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the lower point mem cone ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L53-L79
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeGeometry.lean#L53-L79

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.lower_point_mem_cone_ball (k : ℕ) {t : ℝ} {v : Fin (k + 1) → ℝ}
    (ht0 : 0 < t) (hta : t < a_bg)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ < t / s3_bg) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by sorry
