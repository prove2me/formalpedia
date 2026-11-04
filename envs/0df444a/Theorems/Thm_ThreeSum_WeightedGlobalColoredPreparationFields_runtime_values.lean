-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_runtime_values
-- name    : ThreeSum.WeightedGlobalColoredPreparationFields.runtime_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:23:02.768341+00:00
-- url     : https://prove2.me/theorems/e04d1428-be3a-474c-98a0-1600c5badd83
-- title:
--   Weighted Global Colored Preparation Fields: runtime values
-- statement:
--   The Weighted Global Colored Preparation Fields construction uses the runtime values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L50-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L50-L57

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

theorem ThreeSum.WeightedGlobalColoredPreparationFields.runtime_values (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightWeightedGlobalColoredInitializationProof.runtimeValues n P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F
      (field P n free menu A B C)=
      LightWeightedGlobalColoredInitializationProof.values n (n^κ) (input P n free A B C).free
        (arrays P n free menu A B C).Bmatrix B.length (arrays P n free menu A B C).Cmatrix C.length
        (arrays P n free menu A B C).Omatrix (A.length*2^(J P n))
        (arrays P n free menu A B C).positions menu (J P n) P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F (q P n) := by sorry
