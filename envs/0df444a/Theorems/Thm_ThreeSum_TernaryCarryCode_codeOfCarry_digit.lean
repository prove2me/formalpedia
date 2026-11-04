-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_digit
-- name    : ThreeSum.TernaryCarryCode.codeOfCarry_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:31.158695+00:00
-- url     : https://prove2.me/theorems/1b46a225-d7bf-4e8f-a793-fa0c40b482f8
-- title:
--   Ternary Carry Code: code Of Carry digit
-- statement:
--   The Ternary Carry Code construction uses the code Of Carry digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L46-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L46-L55

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.codeOfCarry_digit {J : ℕ} (c : CarryWord J) (i : Fin J) :
    digit 2 (codeOfCarry c) i.val=(c i.castSucc).val := by sorry
