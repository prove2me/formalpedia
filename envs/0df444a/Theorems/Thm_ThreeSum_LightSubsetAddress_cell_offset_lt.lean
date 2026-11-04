-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
-- name    : ThreeSum.LightSubsetAddress.cell_offset_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:38.775785+00:00
-- url     : https://prove2.me/theorems/f3eda0a1-4731-4335-a59e-d2f3fad486fd
-- title:
--   Light Subset Address: cell offset lt
-- statement:
--   The Light Subset Address construction uses the cell offset lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L29-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L29-L33

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetAddress.cell_offset_lt {W i j : ℕ} (hi : i ≤ W) (hj : j ≤ W) :
    i*(W+1)+j < tableSize W := by sorry
