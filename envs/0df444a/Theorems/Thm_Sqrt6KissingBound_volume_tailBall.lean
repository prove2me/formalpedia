-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volume_tailBall
-- name    : Sqrt6KissingBound.volume_tailBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:04:12.05738+00:00
-- url     : https://prove2.me/theorems/7762094d-2ea4-5455-87b6-697e2007d225
-- title:
--   Sqrt6 Kissing Bound: volume tail Ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume tail Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L27-L31
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L27-L31

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.volume_tailBall (d : ℕ) (r : ℝ) :
    (volume : Measure (Fin d → ℝ)) (tailBall d r) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 r) := by sorry
