-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_cast
-- name    : ThreeSum.TernarySignedReduction.shiftTwo_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:18.844515+00:00
-- url     : https://prove2.me/theorems/ca972753-dc79-4580-b491-55eabf1533f5
-- title:
--   Ternary Signed Reduction: shift Two cast
-- statement:
--   The Ternary Signed Reduction construction uses the shift Two cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L16-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L16-L20

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.shiftTwo_cast {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftTwo U x : ℤ)=x+2*U := by sorry
