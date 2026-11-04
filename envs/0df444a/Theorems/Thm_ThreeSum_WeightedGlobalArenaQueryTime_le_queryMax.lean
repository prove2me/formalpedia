-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTime_le_queryMax
-- name    : ThreeSum.WeightedGlobalArenaQueryTime.le_queryMax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:50:46.812811+00:00
-- url     : https://prove2.me/theorems/8d2a56d9-707d-49c9-8f6d-9ff3342da4fb
-- title:
--   Weighted Global Arena Query Time: le query Max
-- statement:
--   Direct comparison with the already charged tight fixed-type maximum.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L50-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L50-L59

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTime
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup LightWeightedNearPair WeightedGlobalCountFrontendBudget
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalArenaQueryTime.le_queryMax (I : Input) (V : ℕ) :
    WeightedGlobalArenaCountReady.queryTime (m := m) (r := r) I V≤
      WeightedGlobalCountFrontendBudget.queryMax m r
        (nearConfig (m := m) (r := r) I false V) (nearConfig (m := m) (r := r) I true V) := by sorry
