-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_below_bank_or_near
-- name    : ThreeSum.TernaryBank.below_bank_or_near
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:49.018839+00:00
-- url     : https://prove2.me/theorems/319befbe-da28-46a8-8c27-bdc03353a892
-- title:
--   Ternary Bank: below bank or near
-- statement:
--   The Ternary Bank construction uses the below bank or near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L85-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L85-L93

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

theorem ThreeSum.TernaryBank.below_bank_or_near {N T : ℕ} {R Q : TritWord N} (hRQ : Below R Q) :
    R ∈ bank N T ∨ R ∈ nearWords Q (rank Q-(T+1)) := by sorry
