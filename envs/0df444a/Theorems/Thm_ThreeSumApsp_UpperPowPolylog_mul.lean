-- Prove2me | Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mul
-- name    : ThreeSumApsp.UpperPowPolylog.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:13.332899+00:00
-- url     : https://prove2.me/theorems/cca30568-9c75-403e-a12c-8a9b843e32a9
-- title:
--   Upper Pow Polylog: mul
-- statement:
--   `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`, from above, if the second factor is eventually nonnegative.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L123-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean#L123-L128

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Theorems.Thm_ThreeSumApsp_Dominated_mul
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mul
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mul
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mul

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.UpperPowPolylog

theorem ThreeSumApsp.UpperPowPolylog.mul (hf : UpperPowPolylog f a) (hg : UpperPowPolylog g b)
    (hg0 : ∀ᶠ n in atTop, 0 ≤ g n) :
    UpperPowPolylog (fun n => f n * g n) (a + b) := by sorry
