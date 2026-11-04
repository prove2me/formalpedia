-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_bank_downward_closed
-- name    : ThreeSum.TernaryBank.bank_downward_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:37.526925+00:00
-- url     : https://prove2.me/theorems/28c8840c-23e7-4b51-b96a-198f42d9a09d
-- title:
--   Ternary Bank: bank downward closed
-- statement:
--   The Ternary Bank construction uses the bank downward closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L50-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L50-L52

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryBank
open Finset
open ThreeSum.TernaryJointType

theorem ThreeSum.TernaryBank.bank_downward_closed {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (hQ : Q ∈ bank N T) : R ∈ bank N T := by sorry
