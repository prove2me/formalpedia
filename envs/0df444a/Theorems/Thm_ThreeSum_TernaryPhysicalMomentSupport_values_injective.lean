-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_values_injective
-- name    : ThreeSum.TernaryPhysicalMomentSupport.values_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:41.977986+00:00
-- url     : https://prove2.me/theorems/b1c60dba-0e1e-4512-b17f-4229eb220e8d
-- title:
--   Ternary Physical Moment Support: values injective
-- statement:
--   The Ternary Physical Moment Support construction uses the values injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L21-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L21-L24

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

theorem ThreeSum.TernaryPhysicalMomentSupport.values_injective (mode : P → ℤ) : Function.Injective (values mode) := by sorry
