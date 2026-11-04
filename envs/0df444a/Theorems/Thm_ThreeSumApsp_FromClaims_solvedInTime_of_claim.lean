-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedInTime_of_claim
-- name    : ThreeSumApsp.FromClaims.solvedInTime_of_claim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:58.593727+00:00
-- url     : https://prove2.me/theorems/4820b6df-8e2c-4d6c-ab33-9a88f9d4fbd3
-- title:
--   From Claims: solved In Time of claim
-- statement:
--   A claim "solved in `O(n^a)` time on numbers of absolute value at most `n^κ`, for every `κ`", in
--   a reading `S` of "is solved in time T" that is realized, gives programs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L113-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L113-L119

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.solvedInTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperBigOPow a) :
    SolvedInTime Q a 0 := by sorry
