-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_requesterRaw_abs
-- name    : ThreeSum.TernarySignedModes.requesterRaw_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:18.145202+00:00
-- url     : https://prove2.me/theorems/a6c530f9-831a-4a5c-937c-c368c114f162
-- title:
--   Ternary Signed Modes: requester Raw abs
-- statement:
--   The Ternary Signed Modes construction uses the requester Raw abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L32-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L32-L45

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.requesterRaw_abs {U radix J : ℕ} (hb : 1 < radix)
    (a : ℤ) (c : CarryWord J) (k : Coordinate J) :
    |requesterRaw U radix J a c k| ≤ (radix : ℤ) := by sorry
