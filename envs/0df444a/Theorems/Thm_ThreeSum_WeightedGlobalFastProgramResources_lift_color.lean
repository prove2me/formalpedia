-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_lift_color
-- name    : ThreeSum.WeightedGlobalFastProgramResources.lift_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:57:16.678595+00:00
-- url     : https://prove2.me/theorems/e82cd2f0-d556-4ed3-a88a-934e9ee35152
-- title:
--   Weighted Global Fast Program Resources: lift color
-- statement:
--   Relocation of the concrete per-color solver into the actual fast
--   program; the global backend occupies exactly its first fifty procedures.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L83-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L83-L93

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalFastProgramResources.lift_color {lim : Limits} {M b p K κ entry depth T colorMain : ℕ}
    {vals : List ℤ} {μ : ℕ→ℤ} {Post : ℤ→(ℕ→ℤ)→Prop} {color : Program}
    (h : Meets lim color entry depth vals μ T Post) :
    Meets lim (program M b p K κ color colorMain) (50+entry) depth vals μ T Post := by sorry
