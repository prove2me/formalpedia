-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPostABI_argv_zeroCounts_get
-- name    : ThreeSum.WeightedGlobalColoredPostABI.argv_zeroCounts_get
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:14:19.496926+00:00
-- url     : https://prove2.me/theorems/43977f5b-7e84-4f9a-9fdf-b910b1eea589
-- title:
--   Weighted Global Colored Post ABI: argv zero Counts get
-- statement:
--   The Weighted Global Colored Post ABI construction uses the argv zero Counts get property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L86-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPostABI.lean#L86-L93

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

theorem ThreeSum.WeightedGlobalColoredPostABI.argv_zeroCounts_get {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (i : ℕ) (hi : i<106) (h11 : i≠11) (h34 : i≠34) :
    (LightWeightedGlobalCompactReporter.zeroCounts S).argv.getD i 0=S.argv.getD i 0 := by sorry
