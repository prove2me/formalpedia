-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_append
-- name    : ThreeSum.TernaryWantedBatchIndex.cells_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:51.024791+00:00
-- url     : https://prove2.me/theorems/c70ffc74-b4d8-4023-a293-f52ef30ef04f
-- title:
--   Ternary Wanted Batch Index: cells append
-- statement:
--   The Ternary Wanted Batch Index construction uses the cells append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L48-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L48-L49

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_ThreeSum_WantedPairs_cells_append
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.cells_append (xs ys : List Entry) : cells (xs ++ ys) = cells xs ++ cells ys := by sorry
