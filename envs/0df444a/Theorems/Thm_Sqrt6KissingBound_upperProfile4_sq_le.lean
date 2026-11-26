-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperProfile4_sq_le
-- name    : Sqrt6KissingBound.upperProfile4_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:15:59.510837+00:00
-- url     : https://prove2.me/theorems/1f5a390e-993c-57df-86b1-adf6c13fc04a
-- title:
--   Sqrt6 Kissing Bound: upper Profile4 sq le
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Profile4 sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L52-L70
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L52-L70

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.upperProfile4_sq_le {t : ℝ} (hta : a_d4 ≤ t) (ht1 : t ≤ 1) :
    upperProfile4 t ^ 2 ≤ 1 - t ^ 2 := by sorry
