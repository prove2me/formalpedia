-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_predecessor_below
-- name    : ThreeSum.TernaryEuler.predecessor_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:59.131473+00:00
-- url     : https://prove2.me/theorems/10ef85bd-462c-4c41-8ce4-c2969b7ac2c0
-- title:
--   Ternary Euler: predecessor below
-- statement:
--   The Ternary Euler construction uses the predecessor below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L103-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L103-L107

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.predecessor_below {N : ℕ} (R : TritWord N) (i : Fin N) :
    Below (predecessor R i) R := by sorry
