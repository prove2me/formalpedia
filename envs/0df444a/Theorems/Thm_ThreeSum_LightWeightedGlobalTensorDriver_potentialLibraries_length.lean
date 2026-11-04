-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorDriver_potentialLibraries_length
-- name    : ThreeSum.LightWeightedGlobalTensorDriver.potentialLibraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:15:23.44336+00:00
-- url     : https://prove2.me/theorems/5196d96f-d99c-4e5d-a0de-90d05ff6b19b
-- title:
--   Light Weighted Global Tensor Driver: potential Libraries length
-- statement:
--   The Light Weighted Global Tensor Driver construction uses the potential Libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriver.lean#L36-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryQuarticStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorDriver
open Light

theorem ThreeSum.LightWeightedGlobalTensorDriver.potentialLibraries_length (xl yl zl xr yr zr : List ℤ) (K : ℕ) :
    (potentialLibraries xl yl zl xr yr zr K).length=147 := by sorry
