-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
-- name    : ThreeSumApsp.IsPowPolylog.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:34.435407+00:00
-- url     : https://prove2.me/theorems/33843a4a-846a-4b59-a643-65c00025f269
-- title:
--   Is Pow Polylog: mono
-- statement:
--   The exponent may be raised.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L213-L215
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L213-L215

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog

theorem ThreeSumApsp.IsPowPolylog.mono (hf : IsPowPolylog f a) (hab : a ≤ b) : IsPowPolylog f b := by sorry
