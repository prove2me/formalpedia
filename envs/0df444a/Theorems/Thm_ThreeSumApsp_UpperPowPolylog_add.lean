-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_add
-- name    : ThreeSumApsp.UpperPowPolylog.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:39.067651+00:00
-- url     : https://prove2.me/theorems/04d538b3-efbf-4c91-b308-655a7a8998b2
-- title:
--   Upper Pow Polylog: add
-- statement:
--   `Õ(n^a) + Õ(n^a) = Õ(n^a)`, from above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L108-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L108-L113

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_Dominated_add
import Theorems.Thm_ThreeSumApsp_IsBigOPow_add
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_add
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_add

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.add (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g a) :
    UpperPowPolylog (fun n => f n + g n) a := by sorry
