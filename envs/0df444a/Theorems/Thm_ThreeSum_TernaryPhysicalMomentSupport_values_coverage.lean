-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_coverage
-- name    : ThreeSum.TernaryPhysicalMomentSupport.values_coverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:41.064551+00:00
-- url     : https://prove2.me/theorems/b47327a7-d4dc-4530-855e-f8837640dbb5
-- title:
--   Ternary Physical Moment Support: values coverage
-- statement:
--   The Ternary Physical Moment Support construction uses the values coverage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L26-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L26-L29

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

theorem ThreeSum.TernaryPhysicalMomentSupport.values_coverage (mode : P → ℤ) (a : P) : ∃ i, values mode i=mode a := by sorry
