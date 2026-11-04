-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_length
-- name    : ThreeSum.TernaryWantedBatchIndex.cells_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:37.366477+00:00
-- url     : https://prove2.me/theorems/eaddd261-5a4a-4c6e-a7bc-9e86ad477fee
-- title:
--   Ternary Wanted Batch Index: cells length
-- statement:
--   The Ternary Wanted Batch Index construction uses the cells length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L62-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedBatchIndex.lean#L62-L65

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_ThreeSum_WantedPairs_cells_length
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian

theorem ThreeSum.TernaryWantedBatchIndex.cells_length (xs : List Entry) : (cells xs).length = 3 * xs.length := by sorry
