-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_abs_le_of_mem_subMat
-- name    : ThreeSumApsp.Spec.abs_le_of_mem_subMat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:22.278071+00:00
-- url     : https://prove2.me/theorems/4769db83-54e9-4d2f-92a9-fd400024563b
-- title:
--   Spec: abs le of mem sub Mat
-- statement:
--   A bound on the entries of a matrix is a bound on the entries of its blocks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L90-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L90-L92

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.abs_le_of_mem_subMat {s h r0 c0 : ℕ} {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) :
    AbsLe (subMat s h r0 c0 L) U := by sorry
