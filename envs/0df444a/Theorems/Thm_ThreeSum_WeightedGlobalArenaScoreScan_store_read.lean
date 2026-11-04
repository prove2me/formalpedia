-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_store_read
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.store_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:50.928894+00:00
-- url     : https://prove2.me/theorems/45103647-8ef0-4d0e-a356-9c91157feff1
-- title:
--   Weighted Global Arena Score Scan: store read
-- statement:
--   The Weighted Global Arena Score Scan construction uses the store read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L94-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L94-L102

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaScoreScan.store_read {I : Input} {i : ℕ} (hi : i < I.capacity)
    (v : Fin 4→ℤ) (μ : ℕ→ℤ) (c : Fin 4) : store I i v μ (cell I c i)=v c := by sorry
