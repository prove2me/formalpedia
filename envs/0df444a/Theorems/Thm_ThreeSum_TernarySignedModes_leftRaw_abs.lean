-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_leftRaw_abs
-- name    : ThreeSum.TernarySignedModes.leftRaw_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:10.921324+00:00
-- url     : https://prove2.me/theorems/4c00222b-bbda-4dcc-b91b-59e8d7817c96
-- title:
--   Ternary Signed Modes: left Raw abs
-- statement:
--   The Ternary Signed Modes construction uses the left Raw abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L16-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L16-L22

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.leftRaw_abs {U radix J : ℕ} (hb : 1 < radix) (b : ℤ) (k : Coordinate J) :
    |leftRaw U radix J b k| ≤ (radix : ℤ) := by sorry
