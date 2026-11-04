-- Prove2me | Theorems.Thm_ThreeSumApsp_Spec_entry_subMat
-- name    : ThreeSumApsp.Spec.entry_subMat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:11.837388+00:00
-- url     : https://prove2.me/theorems/f00dfdf3-dc75-4c64-b25f-fce5c8ab8fb8
-- title:
--   Spec: entry sub Mat
-- statement:
--   The entry `(i, j)` of a block is the entry `(r0 + i, c0 + j)` of the matrix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L84-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean#L84-L87

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec

theorem ThreeSumApsp.Spec.entry_subMat {s h r0 c0 : ℕ} {L : List ℤ} {i j : ℕ} (hi : i < h) (hj : j < h) :
    entry h (subMat s h r0 c0 L) i j = entry s L (r0 + i) (c0 + j) := by sorry
