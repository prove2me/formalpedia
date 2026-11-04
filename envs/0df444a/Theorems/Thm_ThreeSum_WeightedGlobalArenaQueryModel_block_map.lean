-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_block_map
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.block_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:32:23.507646+00:00
-- url     : https://prove2.me/theorems/2fb6b70a-48c1-4b07-91b7-1c97eeefccd5
-- title:
--   Weighted Global Arena Query Model: block map
-- statement:
--   The Weighted Global Arena Query Model construction uses the block map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L67-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L67-L80

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaQueryModel.block_map (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    {A : Type*} (f : WeightedGlobalGoodOutputCatalog.Record m (Fin F) → A) (fallback : A) :
    (List.ofFn (block maps τ targets positions n j)).map f =
      (descriptor maps τ targets positions n j).2.map
        (fun k => ((WeightedGlobalGoodOutputCatalog.records maps τ).map f).getD k fallback) := by sorry
