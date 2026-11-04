-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_count_total
-- name    : ThreeSum.TernaryTypeLowerBound.count_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:41.595277+00:00
-- url     : https://prove2.me/theorems/67990f36-99e1-4fd1-93f3-511be9dfac60
-- title:
--   Ternary Type Lower Bound: count total
-- statement:
--   The Ternary Type Lower Bound construction uses the count total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L46-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L46-L53

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.count_total {I : Type*} [Fintype I] (w : I → Fin 3) :
    count w 0 + count w 1 + count w 2 = Fintype.card I := by sorry
