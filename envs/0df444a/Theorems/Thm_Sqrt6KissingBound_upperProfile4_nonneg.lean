-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperProfile4_nonneg
-- name    : Sqrt6KissingBound.upperProfile4_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:10:36.29562+00:00
-- url     : https://prove2.me/theorems/a52f7197-cb3b-412d-945b-ec21d7f4cc2b
-- title:
--   Sqrt6 Kissing Bound: upper Profile4 nonneg
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Profile4 nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L25-L30
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L25-L30

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.upperProfile4_nonneg {t : ℝ} (hta : a_d4 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ upperProfile4 t := by sorry
