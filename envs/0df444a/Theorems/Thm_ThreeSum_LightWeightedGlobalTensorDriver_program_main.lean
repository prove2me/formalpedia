-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_program_main
-- name    : ThreeSum.LightWeightedGlobalTensorDriver.program_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:15:43.761215+00:00
-- url     : https://prove2.me/theorems/7f792240-2b8f-4cc2-addb-ad19e2bb92ec
-- title:
--   Light Weighted Global Tensor Driver: program main
-- statement:
--   The Light Weighted Global Tensor Driver construction uses the program main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L44-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L44-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryQuarticStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
import Theorems.Thm_ThreeSum_LightTernaryPairedPotential_program_main
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_program_main
attribute [local simp] ThreeSum.LightTernaryPairedPotential.program_main


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorDriver
open Light

theorem ThreeSum.LightWeightedGlobalTensorDriver.program_main (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (program xl yl zl xr yr zr K)[entry]?=some (body 142 138 149 147) := by sorry
