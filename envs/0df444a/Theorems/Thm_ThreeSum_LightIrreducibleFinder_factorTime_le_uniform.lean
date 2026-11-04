-- Prove2me | Theorems.Thm_ThreeSum_LightIrreducibleFinder_factorTime_le_uniform
-- name    : ThreeSum.LightIrreducibleFinder.factorTime_le_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:23.10519+00:00
-- url     : https://prove2.me/theorems/c573b1fb-5070-4657-835f-b0cb89701193
-- title:
--   Light Irreducible Finder: factor Time le uniform
-- statement:
--   The Light Irreducible Finder construction uses the factor Time le uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L15-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean#L15-L36

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000

theorem ThreeSum.LightIrreducibleFinder.factorTime_le_uniform (C : LightExtensionFactorPredicate.Layout) (q e : ℕ)
    (hp : 1 ≤ C.p) (he : e ≤ C.dim) (hq : C.p^C.dim=q) :
    factorTime C q e ≤ uniformFactorTime C.dim C.p q := by sorry
