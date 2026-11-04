-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_requester_bound
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.requester_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:53:30.641933+00:00
-- url     : https://prove2.me/theorems/ae1c44d4-d5a1-42ae-a08f-5a192de86231
-- title:
--   Weighted Global Arena Selected Signed: requester bound
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the requester bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L110-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L110-L115

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

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.requester_bound {U radix J : ℕ} (hb : 1<radix) (X : ℕ→ℤ) (j i : ℕ) :
    (requester U radix J X j i).natAbs≤radix := by sorry
