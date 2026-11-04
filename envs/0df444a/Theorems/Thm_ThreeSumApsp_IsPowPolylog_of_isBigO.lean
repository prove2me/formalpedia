-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_of_isBigO
-- name    : ThreeSumApsp.IsPowPolylog.of_isBigO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:40.705012+00:00
-- url     : https://prove2.me/theorems/7e55f115-73fd-47fa-aa1a-7b04f03734a9
-- title:
--   Is Pow Polylog: of is Big O
-- statement:
--   If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L199-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L199-L201

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

theorem ThreeSumApsp.IsPowPolylog.of_isBigO (hg : IsPowPolylog g a) (hfg : f =O[atTop] g) : IsPowPolylog f a := by sorry
