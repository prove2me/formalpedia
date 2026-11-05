-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredProgramIdentity_main_lookup
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredProgramIdentity.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:10.141013+00:00
-- url     : https://prove2.me/theorems/dd16c4e9-c806-4e16-aaa6-6da978e310b3
-- title:
--   main_lookup
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L58-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L58-L79

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalFastProgram_main_lookup
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredPrefixCall_main_lookup
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalExecutable_main_lookup

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredProgramIdentity.main_lookup (P : Profile κ) :
    P.color[WeightedGlobalExecutable.colorMain (p:=P.p) P.K]?=
      some (LightWeightedGlobalColoredSolver.body (252+WeightedGlobalExecutable.reportingMain (p:=P.p) P.K)
        P.m P.F P.p (WeightedGlobalLocalParameters.fixedAlpha P.m 2)
        (WeightedGlobalArenaSourceSetup.alphaRank P.m) (TernaryCodeSemantics.address P.output.val)
        (4^(WeightedGlobalLocalParameters.fixedLength P.m)) (P.p^(2*P.K)) P.drift P.scale
        (WeightedGlobalLocalParameters.fixedLength P.m)) := by sorry
