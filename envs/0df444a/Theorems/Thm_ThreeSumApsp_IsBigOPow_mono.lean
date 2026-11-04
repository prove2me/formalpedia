-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
-- name    : ThreeSumApsp.IsBigOPow.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:21.786348+00:00
-- url     : https://prove2.me/theorems/23db4a5b-bd38-4f46-9bb2-30ad32adb739
-- title:
--   Is Big OPow: mono
-- statement:
--   The exponent may be raised.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L78-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L78-L79

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
open ThreeSumApsp.IsBigOPow

theorem ThreeSumApsp.IsBigOPow.mono (hf : IsBigOPow f a) (hab : a ≤ b) : IsBigOPow f b := by sorry
