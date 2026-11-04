-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_grouped_moment
-- name    : ThreeSum.TernaryPhysicalMomentSupport.grouped_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:40.492608+00:00
-- url     : https://prove2.me/theorems/1c5452b4-9290-4c86-8b55-ea64348b151e
-- title:
--   Ternary Physical Moment Support: grouped moment
-- statement:
--   The Ternary Physical Moment Support construction uses the grouped moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L43-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L43-L60

import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryPhysicalMomentSupport.grouped_moment (mode mass : P → ℤ) (k : ℕ) :
    moment (values mode) (weights mode mass) k=∑ a, mass a*mode a^k := by sorry
