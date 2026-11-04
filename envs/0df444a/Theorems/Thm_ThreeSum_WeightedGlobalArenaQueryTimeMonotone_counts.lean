-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_counts
-- name    : ThreeSum.WeightedGlobalArenaQueryTimeMonotone.counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:49:07.494845+00:00
-- url     : https://prove2.me/theorems/c5d3bb5d-8121-4fa4-96ec-491af873721e
-- title:
--   Weighted Global Arena Query Time Monotone: counts
-- statement:
--   The Weighted Global Arena Query Time Monotone construction uses the counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L53-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L53-L57

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

theorem ThreeSum.WeightedGlobalArenaQueryTimeMonotone.counts (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I)≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I') := by sorry
