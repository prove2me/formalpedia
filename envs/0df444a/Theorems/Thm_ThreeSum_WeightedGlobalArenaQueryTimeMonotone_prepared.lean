-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_prepared
-- name    : ThreeSum.WeightedGlobalArenaQueryTimeMonotone.prepared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:42:09.837264+00:00
-- url     : https://prove2.me/theorems/1ae3bd3e-72ab-4525-b0eb-9601e95e3af5
-- title:
--   Weighted Global Arena Query Time Monotone: prepared
-- statement:
--   Physical source keys, addresses and requester values do not enter the
--   query runtime; only the common coefficient magnitude can increase it.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L19-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L19-L34

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_prepared
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] ThreeSum.LightWeightedCountFrontend.prepared


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaQueryTimeMonotone.prepared {V W : ℕ} (I I' : Input) (hV : V≤W) (Q : TritWord (N m r)) :
    LightWeightedPreparedWanted.time
      (nearConfig (m:=m) (r:=r) I false V) (nearConfig (m:=m) (r:=r) I true V) Q≤
    LightWeightedPreparedWanted.time
      (nearConfig (m:=m) (r:=r) I' false W) (nearConfig (m:=m) (r:=r) I' true W) Q := by sorry
