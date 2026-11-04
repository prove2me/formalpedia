-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredProgramIdentity_main_lookup
-- name    : ThreeSum.WeightedGlobalColoredProgramIdentity.main_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:13:32.76026+00:00
-- url     : https://prove2.me/theorems/921e3257-f8ab-494d-a6d8-262807fb941a
-- title:
--   Weighted Global Colored Program Identity: main lookup
-- statement:
--   Exact body lookup for the concrete per-color program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L58-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L58-L79

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_ThreeSum_LightWeightedGlobalFastProgram_main_lookup
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalColoredPrefixCall_main_lookup
import Theorems.Thm_ThreeSum_WeightedGlobalExecutable_main_lookup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredProgramIdentity.main_lookup (P : Profile κ) :
    P.color[WeightedGlobalExecutable.colorMain (p:=P.p) P.K]?=
      some (LightWeightedGlobalColoredSolver.body (252+WeightedGlobalExecutable.reportingMain (p:=P.p) P.K)
        P.m P.F P.p (WeightedGlobalLocalParameters.fixedAlpha P.m 2)
        (WeightedGlobalArenaSourceSetup.alphaRank P.m) (TernaryCodeSemantics.address P.output.val)
        (4^(WeightedGlobalLocalParameters.fixedLength P.m)) (P.p^(2*P.K)) P.drift P.scale
        (WeightedGlobalLocalParameters.fixedLength P.m)) := by sorry
