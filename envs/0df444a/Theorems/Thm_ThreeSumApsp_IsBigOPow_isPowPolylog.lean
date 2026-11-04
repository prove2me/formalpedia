-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_isPowPolylog
-- name    : ThreeSumApsp.IsBigOPow.isPowPolylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:21.717119+00:00
-- url     : https://prove2.me/theorems/992b4def-6dc4-4813-a861-482b9b5c2ea1
-- title:
--   Is Big OPow: is Pow Polylog
-- statement:
--   `O(n^a) ⊆ Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L119-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L119-L120

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

theorem ThreeSumApsp.IsBigOPow.isPowPolylog (hf : IsBigOPow f a) : IsPowPolylog f a := by sorry
