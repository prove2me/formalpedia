-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_length_affL
-- name    : ThreeSumApsp.Spec.length_affL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:17.120932+00:00
-- url     : https://prove2.me/theorems/e2bbd8b8-b170-4fff-b740-9471ba1ca2c0
-- title:
--   Spec: length aff L
-- statement:
--   The list of the numbers `m x + c` is as long as the list of the `x`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L70-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L70-L71

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.length_affL (m c : ℤ) (l : List ℤ) : (affL m c l).length = l.length := by sorry
