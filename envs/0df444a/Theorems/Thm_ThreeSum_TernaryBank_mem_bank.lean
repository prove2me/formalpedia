-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_mem_bank
-- name    : ThreeSum.TernaryBank.mem_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:35.15019+00:00
-- url     : https://prove2.me/theorems/5cd86d35-355d-45bf-b7cb-7b1cc1d503b9
-- title:
--   Ternary Bank: mem bank
-- statement:
--   The Ternary Bank construction uses the mem bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L38-L39

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

theorem ThreeSum.TernaryBank.mem_bank {N T : ℕ} {R : TritWord N} :
    R ∈ bank N T ↔ rank R ≤ T := by sorry
