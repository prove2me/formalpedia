-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_header_eq
-- name    : ThreeSum.WeightedGlobalColoredPreparationFields.header_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:32:07.052752+00:00
-- url     : https://prove2.me/theorems/17cc0cc5-54a9-4a8f-aed0-49b2548f84b1
-- title:
--   Weighted Global Colored Preparation Fields: header eq
-- statement:
--   The Weighted Global Colored Preparation Fields construction uses the header eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L31-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L31-L33

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

theorem ThreeSum.WeightedGlobalColoredPreparationFields.header_eq (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightWeightedGlobalColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C=
      (fields P n free menu A B C).map (fun i=>(i:ℤ)) := by sorry
