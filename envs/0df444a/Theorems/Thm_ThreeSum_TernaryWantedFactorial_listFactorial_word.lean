-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedFactorial_listFactorial_word
-- name    : ThreeSum.TernaryWantedFactorial.listFactorial_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:45.915108+00:00
-- url     : https://prove2.me/theorems/a4bd22a7-7b16-40b0-8aa0-e4e6870a6ad6
-- title:
--   Ternary Wanted Factorial: list Factorial word
-- statement:
--   The Ternary Wanted Factorial construction uses the list Factorial word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L15-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L15-L18

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryWantedFactorial.listFactorial_word {L : ℕ} (w : TritWord L) :
    listFactorial (TernaryBankEnumeration.wordList w)=TernaryConvolution.factorial w := by sorry
