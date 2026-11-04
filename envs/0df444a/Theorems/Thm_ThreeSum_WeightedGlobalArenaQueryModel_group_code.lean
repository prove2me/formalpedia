-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_group_code
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.group_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:35:17.52338+00:00
-- url     : https://prove2.me/theorems/1b25c3f0-aa94-415a-b713-8f88c3cb395a
-- title:
--   Weighted Global Arena Query Model: group code
-- statement:
--   The Weighted Global Arena Query Model construction uses the group code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L111-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L111-L130

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaQueryModel.group_code (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).2.2 =
      Nat.ofDigits F (List.ofFn fun i : Fin r =>
        (Fintype.equivFin (Fin F) (block maps τ targets positions n j i).1).val) := by sorry
