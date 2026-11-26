-- Prove2me | Theorems.Thm_Sqrt6KissingBound_upperProfile3_sq
-- name    : Sqrt6KissingBound.upperProfile3_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:10:27.459405+00:00
-- url     : https://prove2.me/theorems/37bd626c-83f8-4590-a642-f2e97b386115
-- title:
--   Sqrt6 Kissing Bound: upper Profile3 sq
-- statement:
--   The Sqrt6 Kissing Bound construction uses the upper Profile3 sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L29-L31
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L29-L31

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.upperProfile3_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    upperProfile3 t ^ 2 = 1 - t ^ 2 := by sorry
