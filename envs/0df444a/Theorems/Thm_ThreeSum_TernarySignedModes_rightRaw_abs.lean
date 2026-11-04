-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_rightRaw_abs
-- name    : ThreeSum.TernarySignedModes.rightRaw_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:11.915798+00:00
-- url     : https://prove2.me/theorems/99a28664-0b36-48be-a084-1d020b559e36
-- title:
--   Ternary Signed Modes: right Raw abs
-- statement:
--   The Ternary Signed Modes construction uses the right Raw abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L24-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L24-L30

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.rightRaw_abs {U radix J : ℕ} (hb : 1 < radix) (c : ℤ) (k : Coordinate J) :
    |rightRaw U radix J c k| ≤ (radix : ℤ) := by sorry
