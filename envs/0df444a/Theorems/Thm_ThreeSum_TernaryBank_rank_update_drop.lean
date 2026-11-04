-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_rank_update_drop
-- name    : ThreeSum.TernaryBank.rank_update_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:39.302943+00:00
-- url     : https://prove2.me/theorems/6aef5730-7fb3-4e73-bbfc-2171c660e295
-- title:
--   Ternary Bank: rank update drop
-- statement:
--   The Ternary Bank construction uses the rank update drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L78-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L78-L83

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

theorem ThreeSum.TernaryBank.rank_update_drop {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) :
    rank (Function.update R i d) = rank R - ((R i).val - d.val) := by sorry
