-- Prove2me | Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_pos
-- name    : ThreeSum.LightFixedArithmetic.Circuit.bound_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:35.290529+00:00
-- url     : https://prove2.me/theorems/f7890a19-2d31-491e-b7a8-73f4d218c46f
-- title:
--   Circuit: bound pos
-- statement:
--   The Circuit construction uses the bound pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L38-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L38-L44

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light

theorem ThreeSum.LightFixedArithmetic.Circuit.bound_pos (e : Circuit) {U : ℤ} (hU : 0≤U) : 1≤e.bound U := by sorry
