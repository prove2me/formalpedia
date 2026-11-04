-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedFactorial_listFactorial_append
-- name    : ThreeSum.TernaryWantedFactorial.listFactorial_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:34.878563+00:00
-- url     : https://prove2.me/theorems/6e590173-2991-481b-a2ae-62c4db0dbe8c
-- title:
--   Ternary Wanted Factorial: list Factorial append
-- statement:
--   The Ternary Wanted Factorial construction uses the list Factorial append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L11-L13
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedFactorial.lean#L11-L13

import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryWantedFactorial
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedFactorial
open TernaryJointType
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryWantedFactorial.listFactorial_append (xs ys : List ℕ) :
    listFactorial (xs++ys)=listFactorial xs*listFactorial ys := by sorry
