-- Prove2me | Theorems.Thm_Sqrt6KissingBound_standardCoordinates_mem_ball_iff
-- name    : Sqrt6KissingBound.standardCoordinates_mem_ball_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:38.826556+00:00
-- url     : https://prove2.me/theorems/47830e82-f5d5-5174-8cfd-0166d5ec4ab6
-- title:
--   Sqrt6 Kissing Bound: standard Coordinates mem ball iff
-- statement:
--   The Sqrt6 Kissing Bound construction uses the standard Coordinates mem ball iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/StandardGeometry.lean#L38-L57
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/StandardGeometry.lean#L38-L57

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.standardCoordinates_mem_ball_iff (d : ℕ) (t : ℝ) (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ ball 0 1 ↔
      t ^ 2 + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 < 1 := by sorry
