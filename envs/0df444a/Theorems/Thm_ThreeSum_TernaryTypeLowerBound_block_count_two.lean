-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_block_count_two
-- name    : ThreeSum.TernaryTypeLowerBound.block_count_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:30.004236+00:00
-- url     : https://prove2.me/theorems/2f310595-0fb7-4cc8-aba7-1e6dd3d009b3
-- title:
--   Ternary Type Lower Bound: block count two
-- statement:
--   The Ternary Type Lower Bound construction uses the block count two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L40-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L40-L44

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.block_count_two {t1 t2 r : ℕ} (c : BlockChoice t1 t2) :
    count (blockWord (r := r) c) 2 = t2 := by sorry
