-- Prove2me | Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_val
-- name    : ThreeSum.LightFixedArithmetic.Circuit.compile_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:34.142462+00:00
-- url     : https://prove2.me/theorems/71271176-c4a0-463b-9e04-709ce50539dd
-- title:
--   Circuit: compile val
-- statement:
--   The Circuit construction uses the compile val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L57-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L57-L64

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light

theorem ThreeSum.LightFixedArithmetic.Circuit.compile_val (e : Circuit) (atoms : ℕ → Expr) (σ : State) :
    (e.compile atoms).val σ=e.eval (fun i => (atoms i).val σ) := by sorry
