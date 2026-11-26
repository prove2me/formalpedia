-- Prove2me | Theorems.Thm_Sqrt6KissingBound_unit_vector_dim_one_eq_axis_or_neg
-- name    : Sqrt6KissingBound.unit_vector_dim_one_eq_axis_or_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:13:53.537038+00:00
-- url     : https://prove2.me/theorems/e3acb61d-dc28-417d-bd64-b053d09564fe
-- title:
--   Sqrt6 Kissing Bound: unit vector dim one eq axis or neg
-- statement:
--   The Sqrt6 Kissing Bound construction uses the unit vector dim one eq axis or neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionOne.lean#L8-L25
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionOne.lean#L8-L25

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_DimensionOne
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.unit_vector_dim_one_eq_axis_or_neg
    (x : EuclideanSpace ℝ (Fin 1)) (hx : ‖x‖ = 1) :
    x = standardAxis 0 ∨ x = -standardAxis 0 := by sorry
