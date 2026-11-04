-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_query
-- name    : ThreeSum.WeightedGlobalArenaQueryTimeMonotone.query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:41:01.375343+00:00
-- url     : https://prove2.me/theorems/6f28326a-d619-4da4-a5a8-03b375603a47
-- title:
--   Weighted Global Arena Query Time Monotone: query
-- statement:
--   The Weighted Global Arena Query Time Monotone construction uses the query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L36-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L36-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaQueryTimeMonotone.query {V W : ℕ} (I I' : Input) (hV : V≤W) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I V≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' W := by sorry
