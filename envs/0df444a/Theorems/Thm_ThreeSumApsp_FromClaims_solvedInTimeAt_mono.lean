-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedInTimeAt_mono
-- name    : ThreeSumApsp.FromClaims.solvedInTimeAt_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:54.641773+00:00
-- url     : https://prove2.me/theorems/f038e6de-08e6-4b61-bc56-8bfcbcfa70b3
-- title:
--   From Claims: solved In Time At mono
-- statement:
--   The bound `U` is not in the memory: a program for numbers within `n^κ'` serves numbers within
--   `n^κ`, for `κ ≤ κ'`.  (At size 0, where `0^0 > 0^1`, the input is empty.)
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L132-L140
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L132-L140

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.solvedInTimeAt_mono {Q : EndStatement.Problem} (hempty : ∀ x : Q.Instance 0, Q.input x = [])
    {κ κ' : ℕ} (hκ : κ ≤ κ') {a : ℝ} {e : ℕ} (h : SolvedInTimeAt Q κ' a e) :
    SolvedInTimeAt Q κ a e := by sorry
