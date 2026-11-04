-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_triOf_bounded
-- name    : ThreeSumApsp.Spec.triOf_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:05.196256+00:00
-- url     : https://prove2.me/theorems/e5000393-3f00-4087-ada3-dfbc0cc1e658
-- title:
--   Spec: tri Of bounded
-- statement:
--   The weights of the instance read from three lists are bounded if the numbers of the lists
--   are.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L58-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L58-L62

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.triOf_bounded {n U : ℕ} {AB BC AC : List ℤ} (hAB : AbsLe AB U) (hBC : AbsLe BC U)
    (hAC : AbsLe AC U) : (triOf n AB BC AC).WeightsBoundedBy (U : ℤ) := by sorry
