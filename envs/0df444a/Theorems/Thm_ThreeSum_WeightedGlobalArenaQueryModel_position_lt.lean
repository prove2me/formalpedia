-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_position_lt
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:36:26.012077+00:00
-- url     : https://prove2.me/theorems/4923aaef-53d2-4ff3-be5d-456036d139bb
-- title:
--   Weighted Global Arena Query Model: position lt
-- statement:
--   The Weighted Global Arena Query Model construction uses the position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L152-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L152-L157

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_ThreeSum_SourceBuckets_position_lt
import Theorems.Thm_ThreeSum_WeightedGlobalNativeRequesterCoverage_position_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaQueryModel.position_lt (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n originalCount : ℕ) (hpos : ∀ t < n, positions t < originalCount)
    (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).1 < originalCount := by sorry
