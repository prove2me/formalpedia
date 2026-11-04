-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedInPolylogTime_of_claim
-- name    : ThreeSumApsp.FromClaims.solvedInPolylogTime_of_claim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:13:10.176232+00:00
-- url     : https://prove2.me/theorems/c41b2767-d0de-4029-b58d-a8701cab40c9
-- title:
--   From Claims: solved In Polylog Time of claim
-- statement:
--   A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
--   every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L123-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L123-L128

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.solvedInPolylogTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by sorry
