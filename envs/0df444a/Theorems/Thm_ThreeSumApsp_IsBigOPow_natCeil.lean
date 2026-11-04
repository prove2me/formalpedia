-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_natCeil
-- name    : ThreeSumApsp.IsBigOPow.natCeil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:07.409344+00:00
-- url     : https://prove2.me/theorems/63db799b-d0d2-425b-96fc-fcfabf36dfa9
-- title:
--   Is Big OPow: nat Ceil
-- statement:
--   Rounding up keeps the class: if `f = O(n^a)` with `a ≥ 0`, then `⌈f n⌉ = O(n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L125-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L125-L132

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

theorem ThreeSumApsp.IsBigOPow.natCeil (hf : IsBigOPow f a) (ha : 0 ≤ a) :
    IsBigOPow (fun n => (⌈f n⌉₊ : ℝ)) a := by sorry
