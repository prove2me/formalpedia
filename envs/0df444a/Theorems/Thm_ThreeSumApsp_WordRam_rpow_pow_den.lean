-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_rpow_pow_den
-- name    : ThreeSumApsp.WordRam.rpow_pow_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:43.141793+00:00
-- url     : https://prove2.me/theorems/0552602d-76c2-423b-b9d2-28f7c76f3283
-- title:
--   Word Ram: rpow pow den
-- statement:
--   For a rational `r = p/q ≥ 0`: `(n^r)^q = n^p`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L27-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L27-L35

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.rpow_pow_den {r : ℚ} (hr0 : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by sorry
