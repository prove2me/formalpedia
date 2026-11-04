-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_left_bound
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.left_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:51:04.067291+00:00
-- url     : https://prove2.me/theorems/0edc251b-013d-4479-bf0d-ee3434ed240f
-- title:
--   Weighted Global Arena Selected Signed: left bound
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L98-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L98-L102

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.left_bound {U radix J : ℕ} (hb : 1<radix) (B : ℕ→ℤ) (j i : ℕ) :
    (left U radix J B j i).natAbs≤radix := by sorry
