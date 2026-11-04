-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostRecords_cells_left
-- name    : ThreeSum.TernarySourceHostRecords.cells_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:30.508054+00:00
-- url     : https://prove2.me/theorems/3b50676a-f47f-4678-b682-e4b45b54aac8
-- title:
--   Ternary Source Host Records: cells left
-- statement:
--   The Ternary Source Host Records construction uses the cells left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L5-L13
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L5-L13

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySourceHostRecords
open Light

theorem ThreeSum.TernarySourceHostRecords.cells_left (ps : List (ℕ × ℕ)) : ∀ i,
    (WantedPairs.cells ps).getD (2*i) 0=((ps.getD i (0,0)).1 : ℤ) := by sorry
