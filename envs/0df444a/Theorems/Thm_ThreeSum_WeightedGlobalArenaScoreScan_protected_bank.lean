-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_protected_bank
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.protected_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:18:05.097773+00:00
-- url     : https://prove2.me/theorems/489b72c5-582f-4be3-8219-82e96fc92013
-- title:
--   Weighted Global Arena Score Scan: protected bank
-- statement:
--   The Weighted Global Arena Score Scan construction uses the protected bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L38-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L38-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaScoreScan.protected_bank {I : Input} {x : ℕ} (hx : addr I.free I.capacity 13≤x)
    (hy : x < addr I.free I.capacity 16) (hc : 106≤I.capacity) : Protected I x := by sorry
