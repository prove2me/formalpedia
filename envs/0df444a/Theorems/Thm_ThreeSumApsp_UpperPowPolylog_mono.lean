-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
-- name    : ThreeSumApsp.UpperPowPolylog.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:44.174317+00:00
-- url     : https://prove2.me/theorems/28859212-d05e-47c1-a501-dd3c72014146
-- title:
--   Upper Pow Polylog: mono
-- statement:
--   The exponent may be raised.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L103-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L103-L105

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.mono (h : UpperPowPolylog f a) (hab : a ≤ b) : UpperPowPolylog f b := by sorry
