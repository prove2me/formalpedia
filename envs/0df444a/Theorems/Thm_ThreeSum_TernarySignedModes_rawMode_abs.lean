-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_rawMode_abs
-- name    : ThreeSum.TernarySignedModes.rawMode_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:19.221846+00:00
-- url     : https://prove2.me/theorems/52e35f92-81eb-46e9-9e3f-512bf65a094c
-- title:
--   Ternary Signed Modes: raw Mode abs
-- statement:
--   The Ternary Signed Modes construction uses the raw Mode abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L50-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L50-L62

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.rawMode_abs {U radix J : ℕ} (hb : 1 < radix) (b c : ℤ) (k : Coordinate J) :
    |rawMode U radix J b c k| ≤ (radix : ℤ) := by sorry
