-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_source_natAbs_bound
-- name    : ThreeSum.TernarySignedModes.source_natAbs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:18.143384+00:00
-- url     : https://prove2.me/theorems/a44929ca-e6ba-4b69-806c-99991d8958cb
-- title:
--   Ternary Signed Modes: source nat Abs bound
-- statement:
--   The Ternary Signed Modes construction uses the source nat Abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L64-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L64-L74

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.source_natAbs_bound {U radix J : ℕ} (hb : 1 < radix)
    (b c : ℤ) (k : Coordinate J) :
    (leftRaw U radix J b k).natAbs ≤ radix ∧
      (rightRaw U radix J c k).natAbs ≤ radix := by sorry
