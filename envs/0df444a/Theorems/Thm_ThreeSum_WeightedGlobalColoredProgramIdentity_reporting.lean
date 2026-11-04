-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredProgramIdentity_reporting
-- name    : ThreeSum.WeightedGlobalColoredProgramIdentity.reporting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:22:21.097779+00:00
-- url     : https://prove2.me/theorems/738f074c-7752-4524-aa12-fb09d8581aff
-- title:
--   Weighted Global Colored Program Identity: reporting
-- statement:
--   Runtime source counts, keys and pointers do not change the compiled
--   reporter's six local dictionaries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L50-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredProgramIdentity.lean#L50-L55

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPrefixCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredProgramIdentity
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_reporting
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredProgramIdentity
open Light WeightedGlobalConcreteProfile WeightedGlobalArenaSourceSetup
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredProgramIdentity.reporting (P : Profile κ) (r : ℕ) (I : Input) :
    let S:=setup (r:=r) P.maps P.threshold P.cap P.output I
    WeightedGlobalExecutable.reporting P.maps P.cap P.K=
      LightWeightedGlobalPreparedPostSelection.closedProgram S.left.xs S.left.ys S.left.zs
        S.right.xs S.right.ys S.right.zs P.H := by sorry
