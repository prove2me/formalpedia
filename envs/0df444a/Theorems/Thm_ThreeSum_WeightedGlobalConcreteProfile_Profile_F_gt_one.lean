-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_F_gt_one
-- name    : ThreeSum.WeightedGlobalConcreteProfile.Profile.F_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:19:09.079886+00:00
-- url     : https://prove2.me/theorems/cca97a28-e532-4689-ae1b-d89febd3ec33
-- title:
--   Profile: F gt one
-- statement:
--   The Profile construction uses the F gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryConcreteProfile.lean#L82-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryConcreteProfile.lean#L82-L82

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalConcreteProfile
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalCoverScale
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding
open WeightedGlobalArenaFixedParameters WeightedGlobalArenaBudgetExistence
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
open ThreeSum.WeightedGlobalConcreteProfile.Profile
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalConcreteProfile.Profile.F_gt_one (P : Profile κ) : 1<P.F := by sorry
