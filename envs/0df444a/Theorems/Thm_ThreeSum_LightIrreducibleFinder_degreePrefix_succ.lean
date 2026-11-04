-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreePrefix_succ
-- name    : ThreeSum.LightIrreducibleFinder.degreePrefix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:23.243357+00:00
-- url     : https://prove2.me/theorems/061678a3-314c-47e4-a192-45cee4f0fead
-- title:
--   Light Irreducible Finder: degree Prefix succ
-- statement:
--   The Light Irreducible Finder construction uses the degree Prefix succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L60-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean#L60-L68

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

theorem ThreeSum.LightIrreducibleFinder.degreePrefix_succ (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (∀ t<j+1, factorFirst C q f (t+1)=0) ↔
      (∀ t<j, factorFirst C q f (t+1)=0) ∧ factorFirst C q f (j+1)=0 := by sorry
