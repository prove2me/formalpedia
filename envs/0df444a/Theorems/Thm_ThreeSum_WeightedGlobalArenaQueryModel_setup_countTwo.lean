-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_countTwo
-- name    : ThreeSum.WeightedGlobalArenaQueryModel.setup_countTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:37:28.14008+00:00
-- url     : https://prove2.me/theorems/94a45d4f-8fe2-4722-acd4-4967c93b94b1
-- title:
--   Weighted Global Arena Query Model: setup count Two
-- statement:
--   The Weighted Global Arena Query Model construction uses the setup count Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L189-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryModel.lean#L189-L193

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaQueryModel.setup_countTwo {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : WeightedGlobalGoodOutputCatalog.Output m} {I : WeightedGlobalArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    digitCount ((WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) 2 = r*fixedPi m 2 := by sorry
