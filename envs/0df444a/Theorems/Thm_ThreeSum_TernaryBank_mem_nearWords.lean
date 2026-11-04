-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
-- name    : ThreeSum.TernaryBank.mem_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:35.175932+00:00
-- url     : https://prove2.me/theorems/22f2ff22-3221-46e1-84c0-e26aa2f5f2d1
-- title:
--   Ternary Bank: mem near Words
-- statement:
--   The Ternary Bank construction uses the mem near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L44-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L44-L45

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

theorem ThreeSum.TernaryBank.mem_nearWords {N D : ℕ} {R Q : TritWord N} :
    R ∈ nearWords Q D ↔ Below R Q ∧ deficit Q R ≤ D := by sorry
