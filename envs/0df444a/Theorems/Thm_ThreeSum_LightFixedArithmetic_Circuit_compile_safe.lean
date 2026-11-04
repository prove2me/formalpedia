-- Prove2me | Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_compile_safe
-- name    : ThreeSum.LightFixedArithmetic.Circuit.compile_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:13.079953+00:00
-- url     : https://prove2.me/theorems/852d7938-29cc-4ccc-806f-ab273f34e1b8
-- title:
--   Circuit: compile safe
-- statement:
--   The Circuit construction uses the compile safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L66-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean#L66-L102

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedArithmetic
open Light

theorem ThreeSum.LightFixedArithmetic.Circuit.compile_safe (e : Circuit) (atoms : ℕ → Expr) (σ : State)
    {lim : Limits} {U : ℤ} (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U) (hw : e.bound U≤lim.word) :
    (e.compile atoms).Safe lim σ := by sorry
