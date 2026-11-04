-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_abs_entry_le
-- name    : ThreeSumApsp.Spec.abs_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:03.588738+00:00
-- url     : https://prove2.me/theorems/ab345f2a-d885-4b20-8078-b3baab4d4cf6
-- title:
--   Spec: abs entry le
-- statement:
--   A bound on the numbers of the list is a bound on the entries of the matrix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L36-L38

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.abs_entry_le (n : ℕ) {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) (i j : ℕ) :
    |entry n L i j| ≤ U := by sorry
