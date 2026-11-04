-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_support_representation
-- name    : ThreeSum.TernaryPhysicalMomentSupport.support_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:35.209221+00:00
-- url     : https://prove2.me/theorems/a6207147-db2a-4d29-924e-2c836833d9ef
-- title:
--   Ternary Physical Moment Support: support representation
-- statement:
--   The Ternary Physical Moment Support construction uses the support representation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L73-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L73-L81

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

theorem ThreeSum.TernaryPhysicalMomentSupport.support_representation (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    {H : ℕ} (hH : (support mode).card≤H) :
    ∃ t≤H, ∃ v w : Fin t → ℤ, Function.Injective v ∧
      (∀ i, w i≠0) ∧ (∀ k, moment v w k=∑ a, mass a*mode a^k) ∧
      (∀ target, (∃ i, v i=target) ↔ ∃ a, mode a=target) := by sorry
