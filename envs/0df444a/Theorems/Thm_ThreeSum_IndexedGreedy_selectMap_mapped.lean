-- Prove2me | Theorems.Thm_ThreeSum_IndexedGreedy_selectMap_mapped
-- name    : ThreeSum.IndexedGreedy.selectMap_mapped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:35.142494+00:00
-- url     : https://prove2.me/theorems/e60e9a09-cad5-4cb5-8a00-248a280d07d4
-- title:
--   Indexed Greedy: select Map mapped
-- statement:
--   The Indexed Greedy construction uses the select Map mapped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L52-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L52-L60

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum

theorem ThreeSum.IndexedGreedy.selectMap_mapped {α : Type*} [Inhabited α]
    {U : Type*} [DecidableEq U]
    (g : ℕ → α) (covers : α → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap ((List.range n).map g) covers targets =
      g (least (fun i => -((targets.filter (covers (g i))).card : ℤ)) n) := by sorry
