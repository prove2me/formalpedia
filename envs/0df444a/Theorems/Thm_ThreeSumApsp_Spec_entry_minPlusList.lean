-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_entry_minPlusList
-- name    : ThreeSumApsp.Spec.entry_minPlusList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:19.597354+00:00
-- url     : https://prove2.me/theorems/a76490f4-4c34-412a-868e-bb5a1d8a51d5
-- title:
--   Spec: entry min Plus List
-- statement:
--   The entry `(i, j)` of the product stands at the place `i n + j`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L133-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L133-L137

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.entry_minPlusList {n : ℕ} (A B : List ℤ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (minPlusList n A B) i j = minPlusEntry n A B i j := by sorry
