-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_bank_card_le
-- name    : ThreeSum.TernaryBank.bank_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:47.347527+00:00
-- url     : https://prove2.me/theorems/51a61f51-5d70-4fa2-9967-b6d0bc76ced8
-- title:
--   Ternary Bank: bank card le
-- statement:
--   The Ternary Bank construction uses the bank card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L95-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L95-L98

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

theorem ThreeSum.TernaryBank.bank_card_le (N T : ℕ) : (bank N T).card ≤ 3 ^ N := by sorry
