-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_predecessor_rank_lt
-- name    : ThreeSum.TernaryEuler.predecessor_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:52.167632+00:00
-- url     : https://prove2.me/theorems/32ac813b-9a61-49d0-8d9f-00f06cce3892
-- title:
--   Ternary Euler: predecessor rank lt
-- statement:
--   The Ternary Euler construction uses the predecessor rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L86-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L86-L101

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.predecessor_rank_lt {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0 < (R i).val) : rank (predecessor R i) < rank R := by sorry
