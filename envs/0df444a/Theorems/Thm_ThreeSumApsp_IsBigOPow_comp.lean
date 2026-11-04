-- Prove2me | Theorems.Thm_ThreeSumApsp_IsBigOPow_comp
-- name    : ThreeSumApsp.IsBigOPow.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:56.443193+00:00
-- url     : https://prove2.me/theorems/f1e8ef61-e33d-436a-8ebd-339ee5c42d11
-- title:
--   Is Big OPow: comp
-- statement:
--   Substituting a size: if `G(s) = O(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
--   `G(size n) = O(n^(a μ))`. The sizes need not tend to infinity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L308-L314
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean#L308-L314

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

theorem ThreeSumApsp.IsBigOPow.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsBigOPow G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsBigOPow (fun n => G (size n)) (a * μ) := by sorry
