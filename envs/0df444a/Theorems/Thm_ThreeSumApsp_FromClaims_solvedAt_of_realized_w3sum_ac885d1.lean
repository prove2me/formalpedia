-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized_w3sum_ac885d1
-- name    : ThreeSumApsp.FromClaims.solvedAt_of_realized_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:46.771386+00:00
-- url     : https://prove2.me/theorems/484a229b-67c1-4cc4-a568-ecf9a7805ced
-- title:
--   From Claims: solved At of realized
-- statement:
--   From a realized running time with a bound for all large sizes to a program with that bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L89-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L89-L109

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.solvedAt_of_realized_w3sum_ac885d1 {Q : EndStatement.Problem} (T : ℕ → ℝ → ℝ) (κ : ℕ)
    (hR : Realized Q T) {C a : ℝ} {e : ℕ}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ ((κ : ℕ) : ℝ)) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) :
    SolvedInTimeAt Q κ a e := by sorry
