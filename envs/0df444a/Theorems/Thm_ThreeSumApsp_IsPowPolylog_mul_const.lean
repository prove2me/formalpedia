-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul_const
-- name    : ThreeSumApsp.IsPowPolylog.mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:18:44.589233+00:00
-- url     : https://prove2.me/theorems/b51e84b3-485a-4f4c-ad50-6b1d7fa8f4fe
-- title:
--   Is Pow Polylog: mul const
-- statement:
--   Constant factors are absorbed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L231-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L231-L232

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_mul_const

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog

theorem ThreeSumApsp.IsPowPolylog.mul_const (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => f n * c) a := by sorry
