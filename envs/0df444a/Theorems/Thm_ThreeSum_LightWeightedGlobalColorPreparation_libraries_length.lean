-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_libraries_length
-- name    : ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:38.630208+00:00
-- url     : https://prove2.me/theorems/7e96e4a7-bfe3-483e-8f5e-410abec7877d
-- title:
--   Light Weighted Global Color Preparation: libraries length
-- statement:
--   The Light Weighted Global Color Preparation construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L71-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L71-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Theorems.Thm_ThreeSum_LightWeightedGlobalGlobalPrelude_libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparation
open Light
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalColorPreparation.libraries_length : libraries.length=50 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColorPreparation.libraries_length
