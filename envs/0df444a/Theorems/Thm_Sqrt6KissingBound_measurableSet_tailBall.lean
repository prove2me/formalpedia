-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_tailBall
-- name    : Sqrt6KissingBound.measurableSet_tailBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:18:22.498512+00:00
-- url     : https://prove2.me/theorems/94b53d73-b3a0-5446-a0d2-7a1408c4c9e2
-- title:
--   Sqrt6 Kissing Bound: measurable Set tail Ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set tail Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L24-L25
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L24-L25

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.measurableSet_tailBall (d : ℕ) (r : ℝ) : MeasurableSet (tailBall d r) := by sorry
