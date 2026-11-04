-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalUniformQueryTime_le_maximum
-- name    : ThreeSum.WeightedGlobalUniformQueryTime.le_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:12:56.762076+00:00
-- url     : https://prove2.me/theorems/698ccdbb-265b-4c09-af3e-992782cd6936
-- title:
--   Weighted Global Uniform Query Time: le maximum
-- statement:
--   The Weighted Global Uniform Query Time construction uses the le maximum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L26-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryUniformQueryTime.lean#L26-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalUniformQueryTime
open WeightedGlobalArenaSourceSetup WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalActualPrefixRuntime WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalUniformQueryTime.le_maximum (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    {j R : ℕ} (hj : j≤R) :
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=j) I (valueCap (r:=j) maps cap I)≤
      maximum maps cap I R := by sorry
