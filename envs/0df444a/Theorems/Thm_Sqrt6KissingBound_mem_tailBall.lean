-- Prove2me | Theorems.Thm_Sqrt6KissingBound_mem_tailBall
-- name    : Sqrt6KissingBound.mem_tailBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:03:25.607457+00:00
-- url     : https://prove2.me/theorems/b0b731c0-c9c4-5f3a-a6d0-284f3b6deb5c
-- title:
--   Sqrt6 Kissing Bound: mem tail Ball
-- statement:
--   The Sqrt6 Kissing Bound construction uses the mem tail Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L19-L22
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileVolume.lean#L19-L22

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

theorem Sqrt6KissingBound.mem_tailBall {d : ℕ} {r : ℝ} {v : Fin d → ℝ} :
    v ∈ tailBall d r ↔
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ < r := by sorry
