-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowPolylog_comp
-- name    : ThreeSumApsp.IsPowPolylog.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:07.062147+00:00
-- url     : https://prove2.me/theorems/6d7d65b4-4a48-4634-b187-19c79438c920
-- title:
--   Is Pow Polylog: comp
-- statement:
--   Substituting a size: if `G(s) = Õ(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
--   `G(size n) = Õ(n^(a μ))`. The sizes need not tend to infinity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L318-L326
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L318-L326

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Theorems.Thm_ThreeSumApsp_Dominated_comp

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}

theorem ThreeSumApsp.IsPowPolylog.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsPowPolylog G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsPowPolylog (fun n => G (size n)) (a * μ) := by sorry
