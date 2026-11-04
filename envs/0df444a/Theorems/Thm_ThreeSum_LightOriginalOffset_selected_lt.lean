-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt
-- name    : ThreeSum.LightOriginalOffset.selected_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:43.567188+00:00
-- url     : https://prove2.me/theorems/5efe437f-b3df-4e11-b6db-0f5befc5a209
-- title:
--   Light Original Offset: selected lt
-- statement:
--   The Light Original Offset construction uses the selected lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L26-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L26-L27

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

theorem ThreeSum.LightOriginalOffset.selected_lt (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) :
    selected p left right nLeft nRight < p := by sorry
