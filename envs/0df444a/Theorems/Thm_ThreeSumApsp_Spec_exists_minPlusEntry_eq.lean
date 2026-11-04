-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_exists_minPlusEntry_eq
-- name    : ThreeSumApsp.Spec.exists_minPlusEntry_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:44.644477+00:00
-- url     : https://prove2.me/theorems/860ee8b4-b7fe-4152-83b9-c1d1c146f1ef
-- title:
--   Spec: exists min Plus Entry eq
-- statement:
--   An entry of the product is one of the sums.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L116-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L116-L120

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.exists_minPlusEntry_eq {n : ℕ} (hn : 1 ≤ n) (A B : List ℤ) (i j : ℕ) :
    ∃ k < n, minPlusEntry n A B i j = entry n A i k + entry n B k j := by sorry
