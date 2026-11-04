-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_target_row
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.target_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:43:29.225905+00:00
-- url     : https://prove2.me/theorems/27e0e4fa-e82f-400e-bdf7-ef71a0f9886a
-- title:
--   Weighted Global Arena Query Model: target row
-- statement:
--   The Weighted Global Arena Query Model construction uses the target row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryNative.lean#L35-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryNative.lean#L35-L49

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverHashes
open TernaryWantedBatchIndex TernaryExtensionEncoding
variable {m p F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalArenaQueryModel.target_row (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    (row : Fin r → ZMod p)
    (htarget : targets (descriptor maps τ targets positions n j).1 = (coefficientCode row : ℤ)) :
    nativeRow maps τ targets positions n j = row := by sorry
