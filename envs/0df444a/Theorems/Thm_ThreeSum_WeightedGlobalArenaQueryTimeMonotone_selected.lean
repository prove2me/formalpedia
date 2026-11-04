-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_selected
-- name    : ThreeSum.WeightedGlobalArenaQueryTimeMonotone.selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:43:22.740296+00:00
-- url     : https://prove2.me/theorems/88f86fdf-615b-4384-8396-409c8147fae4
-- title:
--   Weighted Global Arena Query Time Monotone: selected
-- statement:
--   Singleton compaction lowers the actual native query coefficient bound;
--   the target hash and compact source values may vary freely.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L61-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryTimeMonotone.lean#L61-L71

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

theorem ThreeSum.WeightedGlobalArenaQueryTimeMonotone.selected {J : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    let I' := WeightedGlobalArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I')≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I) := by sorry
