-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_minPlusEntry_le
-- name    : ThreeSumApsp.Spec.minPlusEntry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:17.90381+00:00
-- url     : https://prove2.me/theorems/f37099a2-2824-4f15-bc7b-e31385541aeb
-- title:
--   Spec: min Plus Entry le
-- statement:
--   An entry of the product is at most each of the sums.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L111-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L111-L113

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.minPlusEntry_le (n : ℕ) (A B : List ℤ) (i j : ℕ) {k : ℕ} (hk : k < n) :
    minPlusEntry n A B i j ≤ entry n A i k + entry n B k j := by sorry
