-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectedSigned_right_bound
-- name    : ThreeSum.WeightedGlobalArenaSelectedSigned.right_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:51:26.788222+00:00
-- url     : https://prove2.me/theorems/687f9c88-302d-44d8-867b-9118cadf72d3
-- title:
--   Weighted Global Arena Selected Signed: right bound
-- statement:
--   The Weighted Global Arena Selected Signed construction uses the right bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L104-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectedSigned.lean#L104-L108

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedTerminal
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Definitions.Def_Submission_Weighted_Global_TernaryArenaNativeComplete
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectedSigned
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSelectedTerminal WeightedGlobalArenaBudgetExistence WeightedGlobalCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaSelectedSigned.right_bound {U radix J : ℕ} (hb : 1<radix) (C : ℕ→ℤ) (j i : ℕ) :
    (right U radix J C j i).natAbs≤radix := by sorry
