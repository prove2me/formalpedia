-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volumeReal_union_of_subsets_ball
-- name    : Sqrt6KissingBound.volumeReal_union_of_subsets_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:08.304038+00:00
-- url     : https://prove2.me/theorems/3879a27e-8dda-41d8-a9c3-613ef00c3923
-- title:
--   Sqrt6 Kissing Bound: volume Real union of subsets ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume Real union of subsets ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BodyVolumeAdditivity.lean#L9-L18
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BodyVolumeAdditivity.lean#L9-L18

import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.volumeReal_union_of_subsets_ball {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hd : Disjoint S T) (hT : MeasurableSet T)
    (hSball : S ⊆ ball 0 1) (hTball : T ⊆ ball 0 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (S ∪ T) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real S +
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real T := by sorry
