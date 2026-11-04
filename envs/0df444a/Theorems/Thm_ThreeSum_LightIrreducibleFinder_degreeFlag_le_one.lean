-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreeFlag_le_one
-- name    : ThreeSum.LightIrreducibleFinder.degreeFlag_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:57.625675+00:00
-- url     : https://prove2.me/theorems/8cc2667b-73de-48c2-994d-73ca1b2c7be4
-- title:
--   Light Irreducible Finder: degree Flag le one
-- statement:
--   The Light Irreducible Finder construction uses the degree Flag le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L57-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L57-L58

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

theorem ThreeSum.LightIrreducibleFinder.degreeFlag_le_one (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) : degreeFlag C q f j≤1 := by sorry
