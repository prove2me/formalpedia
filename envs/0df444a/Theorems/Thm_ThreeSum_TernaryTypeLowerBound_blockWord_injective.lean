-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeLowerBound_blockWord_injective
-- name    : ThreeSum.TernaryTypeLowerBound.blockWord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:30.335691+00:00
-- url     : https://prove2.me/theorems/13a3ce8e-042e-4d19-9415-c89bbbfcfb2c
-- title:
--   Ternary Type Lower Bound: block Word injective
-- statement:
--   The Ternary Type Lower Bound construction uses the block Word injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L55-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean#L55-L66

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryTypeLowerBound.blockWord_injective {t1 t2 r : ℕ} :
    Function.Injective (blockWord (t1 := t1) (t2 := t2) (r := r)) := by sorry
