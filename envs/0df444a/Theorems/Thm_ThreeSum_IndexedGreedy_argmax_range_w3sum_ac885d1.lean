-- Prove2me | Theorems.Thm_ThreeSum_IndexedGreedy_argmax_range_w3sum_ac885d1
-- name    : ThreeSum.IndexedGreedy.argmax_range_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:40.121557+00:00
-- url     : https://prove2.me/theorems/92010a0f-be01-4198-bc2a-9781ff1925c9
-- title:
--   Indexed Greedy: argmax range
-- statement:
--   The Indexed Greedy construction uses the argmax range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L16-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L16-L29

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum

theorem ThreeSum.IndexedGreedy.argmax_range_w3sum_ac885d1 (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    (List.range n).argmax f = some (least (fun i => -(f i : ℤ)) n) := by sorry
