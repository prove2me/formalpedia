-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_protected_ne
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.cell_protected_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:36.079546+00:00
-- url     : https://prove2.me/theorems/abe7aaa8-f73c-41a3-9bc2-f988ef4b331b
-- title:
--   Weighted Global Arena Score Scan: cell protected ne
-- statement:
--   The Weighted Global Arena Score Scan construction uses the cell protected ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L75-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L75-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaScoreScan.cell_protected_ne {I : Input} {c i x : ℕ}
    (hc : c < 4) (hi : i < I.capacity) (hx : Protected I x) : x≠cell I c i := by sorry
