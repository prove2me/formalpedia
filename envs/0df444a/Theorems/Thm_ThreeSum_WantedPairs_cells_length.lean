-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_cells_length
-- name    : ThreeSum.WantedPairs.cells_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:56.771512+00:00
-- url     : https://prove2.me/theorems/729a18d9-7813-4b1f-b44a-9d9547772f50
-- title:
--   Wanted Pairs: cells length
-- statement:
--   The Wanted Pairs construction uses the cells length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L104-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L104-L107

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.cells_length (ps : List (ℕ × ℕ)) : (cells ps).length = 2 * ps.length := by sorry
