-- Prove2me | Theorems.Thm_ThreeSum_IndexedGreedy_argmax_map
-- name    : ThreeSum.IndexedGreedy.argmax_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:46.751833+00:00
-- url     : https://prove2.me/theorems/123c7edc-fa25-470a-8c02-9c5a2883d6d0
-- title:
--   Indexed Greedy: argmax map
-- statement:
--   The Indexed Greedy construction uses the argmax map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L31-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/IndexedGreedy.lean#L31-L41

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum

theorem ThreeSum.IndexedGreedy.argmax_map {α β : Type*} (g : α → β) (f : β → ℕ) (xs : List α) :
    (xs.map g).argmax f = (xs.argmax (f ∘ g)).map g := by sorry
