-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredExecutionTime_preparation
-- name    : ThreeSum.WeightedGlobalColoredExecutionTime.preparation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T03:42:21.48875+00:00
-- url     : https://prove2.me/theorems/69b3159d-41e8-421f-b210-f2928eefac09
-- title:
--   Weighted Global Colored Execution Time: preparation
-- statement:
--   The driver can pay for the first call and its branch before the
--   normalization output lists are known.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredExecutionTime.lean#L22-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredExecutionTime.lean#L22-L29

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryColoredExecutionTime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredExecutionTime
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup
variable {κ : ℕ}
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalColoredExecutionTime.preparation (P : Profile κ) (n free menu c : ℕ) (μ : ℕ→ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
    (hcutoff : P.cutoff≤n) :
    LightWeightedGlobalColorPreparationProof.time n (J P n) (n^κ)+10000≤P.colorTime n := by sorry
