-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_post_cost
-- name    : ThreeSum.WeightedGlobalColoredPostABI.post_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:10:52.840675+00:00
-- url     : https://prove2.me/theorems/32495b60-cbfe-43f1-a7b2-d0ae2a8ac9c8
-- title:
--   Weighted Global Colored Post ABI: post cost
-- statement:
--   The Weighted Global Colored Post ABI construction uses the post cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L172-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L172-L172

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.post_cost : (postArgs.map Expr.cost).sum=671 := by sorry

attribute [defeq] ThreeSum.WeightedGlobalColoredPostABI.post_cost
