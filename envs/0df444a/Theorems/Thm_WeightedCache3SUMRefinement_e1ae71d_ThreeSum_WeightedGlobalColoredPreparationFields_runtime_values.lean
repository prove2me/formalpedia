-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPreparationFields_runtime_values
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields.runtime_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:10:17.638029+00:00
-- url     : https://prove2.me/theorems/34d5c66f-924c-44ac-a53c-0a5661d4582d
-- title:
--   runtime_values
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L50-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L50-L57

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields.runtime_values (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightWeightedGlobalColoredInitializationProof.runtimeValues n P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F
      (field P n free menu A B C)=
      LightWeightedGlobalColoredInitializationProof.values n (n^κ) (input P n free A B C).free
        (arrays P n free menu A B C).Bmatrix B.length (arrays P n free menu A B C).Cmatrix C.length
        (arrays P n free menu A B C).Omatrix (A.length*2^(J P n))
        (arrays P n free menu A B C).positions menu (J P n) P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F (q P n) := by sorry
