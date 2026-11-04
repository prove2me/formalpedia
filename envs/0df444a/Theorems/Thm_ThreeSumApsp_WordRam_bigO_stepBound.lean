-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_bigO_stepBound
-- name    : ThreeSumApsp.WordRam.bigO_stepBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:44.364234+00:00
-- url     : https://prove2.me/theorems/159280b5-d5b1-49f2-9faa-b5e1c1a12569
-- title:
--   Word Ram: big O step Bound
-- statement:
--   The rounded bound is `O(n^r)` in the sense of the end statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L56-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Statements/Exponents.lean#L56-L65

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Definitions.Def_Submission_ThreeSumApsp_Statements_Exponents
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : EndStatement.BigO (stepBound C r) r := by sorry
