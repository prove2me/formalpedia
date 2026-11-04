-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
-- name    : ThreeSum.TernaryBank.mem_lowerWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:35.376572+00:00
-- url     : https://prove2.me/theorems/edce3069-4bea-4d5d-8c14-d1c8f0214cd2
-- title:
--   Ternary Bank: mem lower Words
-- statement:
--   The Ternary Bank construction uses the mem lower Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L41-L42

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

theorem ThreeSum.TernaryBank.mem_lowerWords {N : ℕ} {R Q : TritWord N} :
    R ∈ lowerWords Q ↔ Below R Q := by sorry
