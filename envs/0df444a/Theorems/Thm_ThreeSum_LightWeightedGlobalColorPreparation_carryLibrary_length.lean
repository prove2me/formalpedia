-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_carryLibrary_length
-- name    : ThreeSum.LightWeightedGlobalColorPreparation.carryLibrary_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:57:30.003216+00:00
-- url     : https://prove2.me/theorems/906d7704-75b8-4ee6-b042-4958755998bf
-- title:
--   Light Weighted Global Color Preparation: carry Library length
-- statement:
--   The Light Weighted Global Color Preparation construction uses the carry Library length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L70-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L70-L70

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

theorem ThreeSum.LightWeightedGlobalColorPreparation.carryLibrary_length : carryLibrary.length=42 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColorPreparation.carryLibrary_length
