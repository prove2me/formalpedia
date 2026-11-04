-- Prove2me | Theorems.Thm_ThreeSum_TernaryBank_rank_update_add
-- name    : ThreeSum.TernaryBank.rank_update_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:39.116436+00:00
-- url     : https://prove2.me/theorems/21054474-d2cf-4584-835f-027ccb8289f1
-- title:
--   Ternary Bank: rank update add
-- statement:
--   Rank arithmetic used by the physical frozen-coordinate query.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L63-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBank.lean#L63-L76

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

theorem ThreeSum.TernaryBank.rank_update_add {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3) :
    rank (Function.update R i d) + (R i).val = rank R + d.val := by sorry
