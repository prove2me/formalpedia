-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
-- name    : ThreeSum.LightIrreducibleFinder.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:46.632692+00:00
-- url     : https://prove2.me/theorems/80cfe1d7-a877-4d96-9f69-e138755f55aa
-- title:
--   Light Irreducible Finder: program length
-- statement:
--   The Light Irreducible Finder construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L50-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L50-L50

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

theorem ThreeSum.LightIrreducibleFinder.program_length : program.length=16 := by sorry

attribute [defeq] ThreeSum.LightIrreducibleFinder.program_length
