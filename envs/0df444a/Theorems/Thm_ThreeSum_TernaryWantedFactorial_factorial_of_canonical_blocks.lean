-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedFactorial_factorial_of_canonical_blocks
-- name    : ThreeSum.TernaryWantedFactorial.factorial_of_canonical_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:39.068193+00:00
-- url     : https://prove2.me/theorems/911cd4f5-5024-493d-b2f3-486de05b89b4
-- title:
--   Ternary Wanted Factorial: factorial of canonical blocks
-- statement:
--   The Ternary Wanted Factorial construction uses the factorial of canonical blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L33-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L33-L40

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryWantedFactorial.factorial_of_canonical_blocks {N L : ℕ} (Q : TritWord N) (π : DigitType)
    (qs : List (TritWord L)) (hq : ∀ q∈qs, HasType q π)
    (hword : TernaryBankEnumeration.wordList Q=qs.reverse.flatMap TernaryBankEnumeration.wordList) :
    TernaryConvolution.factorial Q=(2 : ℤ)^(qs.length*π 2) := by sorry
