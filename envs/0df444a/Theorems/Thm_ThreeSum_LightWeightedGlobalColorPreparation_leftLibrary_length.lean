-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_leftLibrary_length
-- name    : ThreeSum.LightWeightedGlobalColorPreparation.leftLibrary_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:57:02.474362+00:00
-- url     : https://prove2.me/theorems/7aec6de0-5af1-4125-984d-6f0cac838076
-- title:
--   Light Weighted Global Color Preparation: left Library length
-- statement:
--   The Light Weighted Global Color Preparation construction uses the left Library length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L68-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L68-L68

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparation
open Light
set_option maxRecDepth 20000

theorem ThreeSum.LightWeightedGlobalColorPreparation.leftLibrary_length : leftLibrary.length=32 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColorPreparation.leftLibrary_length
