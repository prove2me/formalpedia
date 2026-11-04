-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTime_bound
-- name    : ThreeSum.WeightedGlobalArenaQueryTime.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:37:44.773801+00:00
-- url     : https://prove2.me/theorems/38fa5635-2976-4307-b2d6-7a35bd322084
-- title:
--   Weighted Global Arena Query Time: bound
-- statement:
--   The concrete native-word maximum used by CountReady has the same
--   entropy bound as the original fixed-type query maximum. The maximum is a
--   proof-only runtime bound and does not add an enumerating program step.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L64-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTime.lean#L64-L79

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTime
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup LightWeightedNearPair WeightedGlobalCountFrontendBudget
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalArenaQueryTime.bound (I : Input) (V : ℕ) :
    (WeightedGlobalArenaCountReady.queryTime (m := m) (r := r) I V : ℝ)≤
      100000*(WeightedGlobalCountFrontendBudget.width (N m r)
        (nearConfig (m := m) (r := r) I false V)
        (nearConfig (m := m) (r := r) I true V) : ℝ)^3*WeightedGlobalCountFrontendBudget.envelope m r := by sorry
