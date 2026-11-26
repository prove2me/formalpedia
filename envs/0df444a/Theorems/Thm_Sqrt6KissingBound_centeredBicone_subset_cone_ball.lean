-- Prove2me | Theorems.Thm_Sqrt6KissingBound_centeredBicone_subset_cone_ball
-- name    : Sqrt6KissingBound.centeredBicone_subset_cone_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:08:29.473775+00:00
-- url     : https://prove2.me/theorems/f06ca592-0174-419d-9001-f403662c1237
-- title:
--   Sqrt6 Kissing Bound: centered Bicone subset cone ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the centered Bicone subset cone ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L48-L65
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBicone.lean#L48-L65

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.centeredBicone_subset_cone_ball {k : ℕ}
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBicone k x ⊆ strictCone x ∩ ball 0 1 := by sorry
