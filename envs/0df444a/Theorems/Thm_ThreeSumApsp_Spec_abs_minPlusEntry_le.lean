-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_abs_minPlusEntry_le
-- name    : ThreeSumApsp.Spec.abs_minPlusEntry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:21.681185+00:00
-- url     : https://prove2.me/theorems/94e8a494-37db-4b3a-a25f-41b0ce1300fd
-- title:
--   Spec: abs min Plus Entry le
-- statement:
--   The entries of the product of two matrices with entries of absolute value at most `U` have
--   absolute value at most `2U`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L124-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L124-L130

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.abs_minPlusEntry_le {n : ℕ} (hn : 1 ≤ n) {A B : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hA : AbsLe A U) (hB : AbsLe B U) (i j : ℕ) : |minPlusEntry n A B i j| ≤ 2 * U := by sorry
