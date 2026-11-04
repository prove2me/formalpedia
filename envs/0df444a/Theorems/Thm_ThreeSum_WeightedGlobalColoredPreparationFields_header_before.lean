-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_header_before
-- name    : ThreeSum.WeightedGlobalColoredPreparationFields.header_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:22:39.015889+00:00
-- url     : https://prove2.me/theorems/3199643f-cef7-470c-86e4-e1263dc17806
-- title:
--   Weighted Global Colored Preparation Fields: header before
-- statement:
--   The Weighted Global Colored Preparation Fields construction uses the header before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L44-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L44-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredPreparationFields.header_before (P : Profile κ) (n free : ℕ) (A B C : List ℤ) :
    headerAt free n (LightColorParametersCosts.width n)+19≤(input P n free A B C).free := by sorry
