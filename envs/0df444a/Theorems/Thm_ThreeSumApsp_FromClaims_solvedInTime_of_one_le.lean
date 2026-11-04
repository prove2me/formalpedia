-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedInTime_of_one_le
-- name    : ThreeSumApsp.FromClaims.solvedInTime_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:13:05.502969+00:00
-- url     : https://prove2.me/theorems/adb6b243-e31c-4f40-8592-2092ad12e672
-- title:
--   From Claims: solved In Time of one le
-- statement:
--   Some claims of the paper are about `κ ≥ 1`; the items are about all `κ`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L143-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L143-L149

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.solvedInTime_of_one_le {Q : EndStatement.Problem}
    (hempty : ∀ x : Q.Instance 0, Q.input x = []) {a : ℝ} {e : ℕ}
    (h : ∀ κ : ℕ, 1 ≤ κ → SolvedInTimeAt Q κ a e) : SolvedInTime Q a e := by sorry
