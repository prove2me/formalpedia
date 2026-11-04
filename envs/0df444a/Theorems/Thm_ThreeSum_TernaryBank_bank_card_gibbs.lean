-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_bank_card_gibbs
-- name    : ThreeSum.TernaryBank.bank_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:51.158446+00:00
-- url     : https://prove2.me/theorems/401d2e3b-359e-4ee1-8f33-281ac022c7ea
-- title:
--   Ternary Bank: bank card gibbs
-- statement:
--   The Ternary Bank construction uses the bank card gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L118-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L118-L130

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

theorem ThreeSum.TernaryBank.bank_card_gibbs (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N T).card * y ^ T ≤ (1 + y + y ^ 2) ^ N := by sorry
