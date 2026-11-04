-- Prove2me | Theorems.Thm_ThreeSum_IndexedGreedy_selectMap_indices
-- name    : ThreeSum.IndexedGreedy.selectMap_indices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:59.983765+00:00
-- url     : https://prove2.me/theorems/660f91e5-ea37-4d5f-94dc-12bdc59f183f
-- title:
--   Indexed Greedy: select Map indices
-- statement:
--   The Indexed Greedy construction uses the select Map indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L43-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L43-L50

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum

theorem ThreeSum.IndexedGreedy.selectMap_indices {U : Type*} [DecidableEq U]
    (covers : ℕ → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap (List.range n) covers targets =
      least (fun i => -((targets.filter (covers i)).card : ℤ)) n := by sorry
