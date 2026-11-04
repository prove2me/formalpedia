-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_cast_pow_eq
-- name    : ThreeSumApsp.FromClaims.cast_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:41.405541+00:00
-- url     : https://prove2.me/theorems/5749e9d6-e691-4161-bc8b-3ec34f2be6da
-- title:
--   From Claims: cast pow eq
-- statement:
--   The bound `U = N^c` on the numbers, as a real number.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L44-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L44-L47

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.cast_pow_eq (N c : ℕ) : ((N ^ c : ℕ) : ℝ) = (N : ℝ) ^ ((c : ℕ) : ℝ) := by sorry
