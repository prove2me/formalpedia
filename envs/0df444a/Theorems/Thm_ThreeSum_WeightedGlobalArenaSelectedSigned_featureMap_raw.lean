-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_featureMap_raw
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.featureMap_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:25.440614+00:00
-- url     : https://prove2.me/theorems/bdb23290-55c1-4f7e-b82e-fe3b9be83b1d
-- title:
--   Weighted Global Arena Selected Signed: feature Map raw
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the feature Map raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L25-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L25-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.featureMap_raw {J : ℕ} (raw : Coordinate J→ℤ) :
    featureMap J (field raw)=(fun i => (feature raw i.val : ZMod p)) := by sorry
