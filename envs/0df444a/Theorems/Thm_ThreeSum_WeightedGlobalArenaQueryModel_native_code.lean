-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_native_code
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.native_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:39:03.253207+00:00
-- url     : https://prove2.me/theorems/debbd509-eee0-4d5c-ae0f-e0b589a72f33
-- title:
--   Weighted Global Arena Query Model: native code
-- statement:
--   The Weighted Global Arena Query Model construction uses the native code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryNative.lean#L25-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryNative.lean#L25-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverHashes
open TernaryWantedBatchIndex TernaryExtensionEncoding
variable {m p F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000

theorem ThreeSum.WeightedGlobalArenaQueryModel.native_code (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    Radix.positionalHash (p : ℤ) (WeightedGlobalGoodOutputCatalog.key maps)
      (List.ofFn (block maps τ targets positions n j)) =
      (coefficientCode (nativeRow maps τ targets positions n j) : ℤ) := by sorry
