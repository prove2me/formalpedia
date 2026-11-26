-- Prove2me | Theorems.Thm_Sqrt6KissingBound_standardCoordinates_mem_strictCone_iff
-- name    : Sqrt6KissingBound.standardCoordinates_mem_strictCone_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:51.829402+00:00
-- url     : https://prove2.me/theorems/44b2c971-3e2a-509c-a490-f5b61e707ca6
-- title:
--   Sqrt6 Kissing Bound: standard Coordinates mem strict Cone iff
-- statement:
--   The Sqrt6 Kissing Bound construction uses the standard Coordinates mem strict Cone iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/StandardGeometry.lean#L59-L69
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/StandardGeometry.lean#L59-L69

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.standardCoordinates_mem_strictCone_iff (d : ℕ) (t : ℝ)
    (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ strictCone (standardAxis d) ↔
      (Real.sqrt 3 / 2) *
          Real.sqrt (t ^ 2 +
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2) < t := by sorry
