-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_shiftOne_cast
-- name    : ThreeSum.TernarySignedReduction.shiftOne_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:24.444779+00:00
-- url     : https://prove2.me/theorems/186dacc5-ce60-4df5-baea-44413c0c78ec
-- title:
--   Ternary Signed Reduction: shift One cast
-- statement:
--   The Ternary Signed Reduction construction uses the shift One cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L11-L14
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L11-L14

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.shiftOne_cast {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftOne U x : ℤ)=x+U := by sorry
