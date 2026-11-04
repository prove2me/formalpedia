-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_lt
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.cell_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:14.500082+00:00
-- url     : https://prove2.me/theorems/b675ee09-19a3-4a29-b730-ae9dff04750e
-- title:
--   Weighted Global Arena Score Scan: cell lt
-- statement:
--   The Weighted Global Arena Score Scan construction uses the cell lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L47-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L47-L51

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaScoreScan.cell_lt {I : Input} {c i : ℕ} (hi : i < I.capacity) :
    cell I c i < addr I.free I.capacity (10+c) := by sorry
