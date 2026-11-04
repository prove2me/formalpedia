-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_BuiltO_transfer
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.BuiltO.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:22:25.173904+00:00
-- url     : https://prove2.me/theorems/a61cc275-dc43-4189-a288-a1332d9c4649
-- title:
--   Built O: transfer
-- statement:
--   The Built O construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L264-L271
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L264-L271

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_ThreeSum_LightTernaryPreparedState_Snapshot_transfer
import Theorems.Thm_ThreeSum_LightWeightedPreparedState_Snapshot_transfer

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.BuiltO.transfer {C : Config} {D : Data C} {μ ν ξ : ℕ → ℤ} {cutoff depth : ℕ}
    (G : AppendGuard C D lim depth μ) (H : BuiltO C D μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.Onew+C.nO≤cutoff) : BuiltO C D μ ξ := by sorry
