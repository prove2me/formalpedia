-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_ne
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.cell_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:33.213805+00:00
-- url     : https://prove2.me/theorems/ccedd112-d9bb-4c29-a535-c5218e232eb8
-- title:
--   Weighted Global Arena Score Scan: cell ne
-- statement:
--   The Weighted Global Arena Score Scan construction uses the cell ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L56-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L56-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaScoreScan.cell_ne {I : Input} {c d i j : ℕ}
    (hi : i < I.capacity) (hj : j < I.capacity) (h : c≠d ∨ i≠j) :
    cell I c i ≠ cell I d j := by sorry
