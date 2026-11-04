-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_lt
-- name    : ThreeSum.TernaryCarryCode.codeOfCarry_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:19.407821+00:00
-- url     : https://prove2.me/theorems/10f0dd22-a270-47ff-b708-20a62c375821
-- title:
--   Ternary Carry Code: code Of Carry lt
-- statement:
--   The Ternary Carry Code construction uses the code Of Carry lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L37-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L37-L44

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.codeOfCarry_lt {J : ℕ} (c : CarryWord J) : codeOfCarry c<2^J := by sorry
