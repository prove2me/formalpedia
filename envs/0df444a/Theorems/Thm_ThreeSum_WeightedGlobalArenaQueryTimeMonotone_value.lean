-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_value
-- name    : ThreeSum.WeightedGlobalArenaQueryTimeMonotone.value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:38:07.679287+00:00
-- url     : https://prove2.me/theorems/0e0ac883-202f-4587-93f8-936365e4c859
-- title:
--   Weighted Global Arena Query Time Monotone: value
-- statement:
--   The Weighted Global Arena Query Time Monotone construction uses the value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L47-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L47-L51

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

theorem ThreeSum.WeightedGlobalArenaQueryTimeMonotone.value (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    valueCap (r:=r) maps cap I≤valueCap (r:=r) maps cap I' := by sorry
