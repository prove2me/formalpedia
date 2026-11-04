-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_valid_last
-- name    : ThreeSum.TernarySignedReduction.valid_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:37.528582+00:00
-- url     : https://prove2.me/theorems/6341432b-fd5c-4105-adc3-0f4c726c5f7f
-- title:
--   Ternary Signed Reduction: valid last
-- statement:
--   The Ternary Signed Reduction construction uses the valid last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L56-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L56-L60

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.valid_last {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) : c (Fin.last J)=0 := by sorry
