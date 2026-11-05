-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalMomentDriver_library_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver.library_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:16:16.059209+00:00
-- url     : https://prove2.me/theorems/829674be-908f-4561-83cd-d1679ff5d910
-- title:
--   library_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L51-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentDriver.lean#L51-L71

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentDriver
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_library

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentDriver.library_meets {lim : Limits} {d i T : ℕ} {vals : List ℤ} {μ : ℕ→ℤ}
    {R : ℤ→(ℕ→ℤ)→Prop} (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ))
    (hi : i<steps.length)
    (h : Meets lim (LightWeightedGlobalMomentSourceProgram.program xl yl zl xr yr zr
      (steps.getD i (0,0)).1 (steps.getD i (0,0)).2) 138 d vals μ T R) :
    Meets lim (library xl yl zl xr yr zr steps) (139*i+138) d vals μ T R := by sorry
