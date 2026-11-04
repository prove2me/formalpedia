-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparation_rightLibrary_length
-- name    : ThreeSum.LightWeightedGlobalColorPreparation.rightLibrary_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:56:28.650888+00:00
-- url     : https://prove2.me/theorems/a1038761-b4bb-40ed-a9e0-959e12b8ad4e
-- title:
--   Light Weighted Global Color Preparation: right Library length
-- statement:
--   The Light Weighted Global Color Preparation construction uses the right Library length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L69-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparation.lean#L69-L69

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

theorem ThreeSum.LightWeightedGlobalColorPreparation.rightLibrary_length : rightLibrary.length=36 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalColorPreparation.rightLibrary_length
