-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow_w3sum_ac885d1
-- name    : ThreeSumApsp.WordRam.bigO_of_le_rpow_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:44.869437+00:00
-- url     : https://prove2.me/theorems/1f9fc834-4292-4f29-9868-e5ade7de09bc
-- title:
--   Word Ram: big O of le rpow
-- statement:
--   A function with `T(n) ≤ C n^r` from `n = 2` on is `O(n^r)` in the sense of the end statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L38-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L38-L50

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.bigO_of_le_rpow_w3sum_ac885d1 {C : ℝ} {r : ℚ} (hr0 : 0 ≤ r) {T : ℕ → ℕ}
    (hT : ∀ n : ℕ, 2 ≤ n → (T n : ℝ) ≤ C * (n : ℝ) ^ (r : ℝ)) : EndStatement.BigO T r := by sorry
