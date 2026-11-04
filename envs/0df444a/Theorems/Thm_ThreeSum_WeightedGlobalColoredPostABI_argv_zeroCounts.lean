-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_argv_zeroCounts
-- name    : ThreeSum.WeightedGlobalColoredPostABI.argv_zeroCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:13:06.890219+00:00
-- url     : https://prove2.me/theorems/82cb4373-80ff-4050-b42f-ad0577e7ad35
-- title:
--   Weighted Global Colored Post ABI: argv zero Counts
-- statement:
--   The Weighted Global Colored Post ABI construction uses the argv zero Counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L83-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L83-L84

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPostABI
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPostABI
open Light LightWeightedGlobalColoredSolver WeightedGlobalArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

theorem ThreeSum.WeightedGlobalColoredPostABI.argv_zeroCounts {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) :
    (LightWeightedGlobalCompactReporter.zeroCounts S).argv=(S.argv.set 11 0).set 34 0 := by sorry
