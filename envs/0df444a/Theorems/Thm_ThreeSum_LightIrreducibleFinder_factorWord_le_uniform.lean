-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_factorWord_le_uniform
-- name    : ThreeSum.LightIrreducibleFinder.factorWord_le_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:18.88758+00:00
-- url     : https://prove2.me/theorems/863a89f9-5b62-4185-904c-63012997b42b
-- title:
--   Light Irreducible Finder: factor Word le uniform
-- statement:
--   The Light Irreducible Finder construction uses the factor Word le uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L38-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L38-L47

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000

theorem ThreeSum.LightIrreducibleFinder.factorWord_le_uniform (C : LightExtensionFactorPredicate.Layout) (q e : ℕ)
    (hp : 1 ≤ C.p) (he : e ≤ C.dim) (hq : C.p^C.dim=q) :
    LightExtensionFactorPredicate.word (atDegree C e) q q ≤ uniformFactorWord C.dim C.p q := by sorry
