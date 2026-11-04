-- Prove2me | Theorems.Thm_ThreeSumApsp_IsPowLittleO_of_eventually_abs_le
-- name    : ThreeSumApsp.IsPowLittleO.of_eventually_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:46:12.624761+00:00
-- url     : https://prove2.me/theorems/e573b88f-a129-4542-aa2c-0ed891212d56
-- title:
--   Is Pow Little O: of eventually abs le
-- statement:
--   If for every `η > 0`, `|f(n)| ≤ n^{a+η}` for all large `n`, then `f(n) = n^{a+o(1)}`. For
--   `ε(n)` take the excess of the exponent that is needed at `n`: the number with
--   `n^{a+ε(n)} = max(|f(n)|, n^a)`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L49-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean#L49-L73

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

theorem ThreeSumApsp.IsPowLittleO.of_eventually_abs_le
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ (a + η)) : IsPowLittleO f a := by sorry
