-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedFactorial_typed_blocks_factorial
-- name    : ThreeSum.TernaryWantedFactorial.typed_blocks_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:37.241814+00:00
-- url     : https://prove2.me/theorems/3c91dac2-ac76-4c01-92b8-c0580d69dafb
-- title:
--   Ternary Wanted Factorial: typed blocks factorial
-- statement:
--   The Ternary Wanted Factorial construction uses the typed blocks factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L20-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L20-L31

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryWantedFactorial.typed_blocks_factorial {L : ℕ} (π : DigitType) (qs : List (TritWord L))
    (hq : ∀ q∈qs, HasType q π) :
    listFactorial (qs.flatMap TernaryBankEnumeration.wordList)=(2 : ℤ)^(qs.length*π 2) := by sorry
