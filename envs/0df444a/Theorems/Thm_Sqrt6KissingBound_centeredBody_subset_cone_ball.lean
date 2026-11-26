-- Prove2me | Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_cone_ball
-- name    : Sqrt6KissingBound.centeredBody_subset_cone_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:09:16.812841+00:00
-- url     : https://prove2.me/theorems/59dc1d45-47ff-46c8-a783-ae3415214f06
-- title:
--   Sqrt6 Kissing Bound: centered Body subset cone ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the centered Body subset cone ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L35-L54
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L35-L54

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.centeredBody_subset_cone_ball {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ strictCone x ∩ ball 0 1 := by sorry
