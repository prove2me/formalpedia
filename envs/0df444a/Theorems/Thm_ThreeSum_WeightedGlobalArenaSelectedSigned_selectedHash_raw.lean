-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_selectedHash_raw
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.selectedHash_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:54:45.935571+00:00
-- url     : https://prove2.me/theorems/088a0450-2e80-4f22-9d0a-5ba2b777ed37
-- title:
--   Weighted Global Arena Selected Signed: selected Hash raw
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the selected Hash raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L36-L38

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

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.selectedHash_raw (A : Inputs) (s : State (p := p) A) (r : ℕ) (raw : Coordinate A.J→ℤ) :
    selectedHash A s r (field raw)=hashMap A s r (fun i => (feature raw i.val : ZMod p)) := by sorry
