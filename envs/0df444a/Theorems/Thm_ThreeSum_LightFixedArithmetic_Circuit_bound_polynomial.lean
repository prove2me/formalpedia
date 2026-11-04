-- Prove2me | Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_polynomial
-- name    : ThreeSum.LightFixedArithmetic.Circuit.bound_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:28.59438+00:00
-- url     : https://prove2.me/theorems/71bea591-b3f8-4ab7-a5fe-934d1a5557c5
-- title:
--   Circuit: bound polynomial
-- statement:
--   The Circuit construction uses the bound polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L127-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L127-L154

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light

theorem ThreeSum.LightFixedArithmetic.Circuit.bound_polynomial (e : Circuit) {U : ℤ} (hU : 0≤U) :
    e.bound U≤e.coefficient*(U+1)^e.degree := by sorry
