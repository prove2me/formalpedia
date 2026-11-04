-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_target_iff
-- name    : ThreeSum.TernaryPhysicalMomentSupport.target_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:43.16095+00:00
-- url     : https://prove2.me/theorems/f38af4b4-4eff-4a73-965e-c6212b1cb589
-- title:
--   Ternary Physical Moment Support: target iff
-- statement:
--   The Ternary Physical Moment Support construction uses the target iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L62-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L62-L71

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

theorem ThreeSum.TernaryPhysicalMomentSupport.target_iff (mode : P → ℤ) (target : ℤ) :
    (∃ i, values mode i=target) ↔ ∃ a, mode a=target := by sorry
