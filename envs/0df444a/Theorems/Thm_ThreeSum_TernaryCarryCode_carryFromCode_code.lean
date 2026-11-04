-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_carryFromCode_code
-- name    : ThreeSum.TernaryCarryCode.carryFromCode_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:20.841306+00:00
-- url     : https://prove2.me/theorems/8331f640-cf3f-440c-905f-b92f97fddcdd
-- title:
--   Ternary Carry Code: carry From Code code
-- statement:
--   The Ternary Carry Code construction uses the carry From Code code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L57-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L57-L67

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.carryFromCode_code {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) :
    carryFromCode J (codeOfCarry c)=c := by sorry
