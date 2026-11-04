-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
-- name    : ThreeSum.TernaryBank.rank_add_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:39.40445+00:00
-- url     : https://prove2.me/theorems/da5a30a4-0d0c-4779-b963-1984d8bf3e0f
-- title:
--   Ternary Bank: rank add deficit
-- statement:
--   The Ternary Bank construction uses the rank add deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L54-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L54-L60

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

theorem ThreeSum.TernaryBank.rank_add_deficit {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    rank R + deficit Q R = rank Q := by sorry
