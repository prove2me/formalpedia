-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColorPreparationLayout_color_end
-- name    : ThreeSum.WeightedGlobalColorPreparationLayout.color_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:16:44.550735+00:00
-- url     : https://prove2.me/theorems/86fd9a40-25bb-446c-a587-d3c645ac5ae2
-- title:
--   Weighted Global Color Preparation Layout: color end
-- statement:
--   The Weighted Global Color Preparation Layout construction uses the color end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L14-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColorPreparationLayout.lean#L14-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColorPreparationLayout.color_end {free n W : ℕ} (hn : 0<n) (hW : LightColorParametersCosts.width n≤W) :
    LightTernaryColorPrelude.space free n≤headerAt free n W := by sorry
