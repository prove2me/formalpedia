-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_shifted_addition_iff
-- name    : ThreeSum.TernarySignedReduction.shifted_addition_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:30.02013+00:00
-- url     : https://prove2.me/theorems/3602f549-e0bf-4512-8048-548ad547864c
-- title:
--   Ternary Signed Reduction: shifted addition iff
-- statement:
--   The Ternary Signed Reduction construction uses the shifted addition iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L38-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L38-L50

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.shifted_addition_iff {U : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ)) :
    shiftOne U b+shiftOne U a=shiftTwo U c ↔ c-b=a := by sorry
