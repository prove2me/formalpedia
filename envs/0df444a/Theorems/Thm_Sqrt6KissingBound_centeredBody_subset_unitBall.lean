-- Prove2me | Theorems.Thm_Sqrt6KissingBound_centeredBody_subset_unitBall
-- name    : Sqrt6KissingBound.centeredBody_subset_unitBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:08:52.481976+00:00
-- url     : https://prove2.me/theorems/0645f5fc-e98a-5832-b5ae-3c790e60db7f
-- title:
--   Sqrt6 Kissing Bound: centered Body subset unit Ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the centered Body subset unit Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L56-L61
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L56-L61

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.centeredBody_subset_unitBall {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ ball 0 1 := by sorry
