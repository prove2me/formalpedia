-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_block_count_one
-- name    : ThreeSum.TernaryTypeLowerBound.block_count_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:30.755343+00:00
-- url     : https://prove2.me/theorems/cedc0ee8-f84d-4ce2-ba7b-ae3848877976
-- title:
--   Ternary Type Lower Bound: block count one
-- statement:
--   The Ternary Type Lower Bound construction uses the block count one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L34-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L34-L38

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.block_count_one {t1 t2 r : ℕ} (c : BlockChoice t1 t2) :
    count (blockWord (r := r) c) 1 = t1 := by sorry
