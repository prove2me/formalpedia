-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_store_other
-- name    : ThreeSum.WeightedGlobalArenaScoreScan.store_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:17:46.342837+00:00
-- url     : https://prove2.me/theorems/5106efb2-1903-44fd-956b-710f85a48bc7
-- title:
--   Weighted Global Arena Score Scan: store other
-- statement:
--   The Weighted Global Arena Score Scan construction uses the store other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaScoreScan.lean#L89-L92

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

theorem ThreeSum.WeightedGlobalArenaScoreScan.store_other {I : Input} {i x : ℕ} {v : Fin 4→ℤ} {μ : ℕ→ℤ}
    (hx : ∀c < 4, x≠cell I c i) : store I i v μ x=μ x := by sorry
