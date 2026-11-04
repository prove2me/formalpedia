-- Prove2me | Theorems.Thm_ThreeSum_TernarySourceHostRecords_cells_right
-- name    : ThreeSum.TernarySourceHostRecords.cells_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:28.439581+00:00
-- url     : https://prove2.me/theorems/8f509307-2161-493f-af5a-4f6d5fa588d2
-- title:
--   Ternary Source Host Records: cells right
-- statement:
--   The Ternary Source Host Records construction uses the cells right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L15-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySourceHostRecords.lean#L15-L23

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_TernarySourceHostRecords
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySourceHostRecords
open Light

theorem ThreeSum.TernarySourceHostRecords.cells_right (ps : List (ℕ × ℕ)) : ∀ i<ps.length,
    (WantedPairs.cells ps).getD (2*i+1) 0=((ps.getD i (0,0)).2 : ℤ) := by sorry
