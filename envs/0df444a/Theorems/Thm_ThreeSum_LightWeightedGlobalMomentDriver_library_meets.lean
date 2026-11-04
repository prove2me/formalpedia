-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalMomentDriver_library_meets
-- name    : ThreeSum.LightWeightedGlobalMomentDriver.library_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:50:11.466113+00:00
-- url     : https://prove2.me/theorems/25b71576-b8cd-4a8b-9c65-49e110ef9b67
-- title:
--   Light Weighted Global Moment Driver: library meets
-- statement:
--   The Light Weighted Global Moment Driver construction uses the library meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L51-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L51-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentDriver
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_library

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000

theorem ThreeSum.LightWeightedGlobalMomentDriver.library_meets {lim : Limits} {d i T : ℕ} {vals : List ℤ} {μ : ℕ→ℤ}
    {R : ℤ→(ℕ→ℤ)→Prop} (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ))
    (hi : i<steps.length)
    (h : Meets lim (LightWeightedGlobalMomentSourceProgram.program xl yl zl xr yr zr
      (steps.getD i (0,0)).1 (steps.getD i (0,0)).2) 138 d vals μ T R) :
    Meets lim (library xl yl zl xr yr zr steps) (139*i+138) d vals μ T R := by sorry
