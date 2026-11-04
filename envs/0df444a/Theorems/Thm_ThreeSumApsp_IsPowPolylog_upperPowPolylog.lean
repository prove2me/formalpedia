-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_upperPowPolylog
-- name    : ThreeSumApsp.IsPowPolylog.upperPowPolylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:07.318016+00:00
-- url     : https://prove2.me/theorems/3c5a5f7e-c486-480e-9d62-2072ffc2b7ec
-- title:
--   Is Pow Polylog: upper Pow Polylog
-- statement:
--   `f = Õ(n^a)` is in particular an upper bound on `f`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L71-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L71-L78

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}

theorem ThreeSumApsp.IsPowPolylog.upperPowPolylog (hf : IsPowPolylog f a) : UpperPowPolylog f a := by sorry
