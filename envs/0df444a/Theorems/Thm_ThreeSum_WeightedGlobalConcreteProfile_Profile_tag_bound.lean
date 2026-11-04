-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_tag_bound
-- name    : ThreeSum.WeightedGlobalConcreteProfile.Profile.tag_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:33:28.215801+00:00
-- url     : https://prove2.me/theorems/f219b7bf-432e-4fe1-b743-24570a4b3e42
-- title:
--   Profile: tag bound
-- statement:
--   The Profile construction uses the tag bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryConcreteProfile.lean#L123-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryConcreteProfile.lean#L123-L124

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

theorem ThreeSum.WeightedGlobalConcreteProfile.Profile.tag_bound (P : Profile κ) : P.radix≤2*(4^fixedLength P.m)+1 := by sorry
