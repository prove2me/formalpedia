-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_fastExecution
-- name    : ThreeSum.WeightedGlobalConcreteProfile.Profile.fastExecution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T04:53:52.919517+00:00
-- url     : https://prove2.me/theorems/9be7b5cd-b9f6-4e51-aa80-e65f05d68d18
-- title:
--   Profile: fast Execution
-- statement:
--   Every coloring invokes the literal proved colored solver on the actual
--   global backend, input segment, and six-cell coloring record.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileFastExecution.lean#L20-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryProfileFastExecution.lean#L20-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryProfileRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryColoredExecution
import Definitions.Def_Submission_Weighted_Global_TernaryProfileFastExecution
import Theorems.Thm_Light_Meets_main
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalConcreteProfile ThreeSum.WeightedGlobalConcreteProfile.Profile
open Light LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalConcreteProfile.Profile.fastExecution (P : Profile κ) :
    TernarySolverEndBridge.FastExecution P.program P.main κ P.cutoff P.fastTime P.need := by sorry
