-- Prove2me | Theorems.Thm_ThreeSum_LightBooleanDot_dot_succ
-- name    : ThreeSum.LightBooleanDot.dot_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:08.935755+00:00
-- url     : https://prove2.me/theorems/56c737b6-1dd7-4800-8648-83769c05073a
-- title:
--   Light Boolean Dot: dot succ
-- statement:
--   The Light Boolean Dot construction uses the dot succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L21-L22

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightBooleanDot.dot_succ (f g : ℕ → ℕ) (j : ℕ) :
    dot f g (j+1) = dot f g j + f j*g j := by sorry
