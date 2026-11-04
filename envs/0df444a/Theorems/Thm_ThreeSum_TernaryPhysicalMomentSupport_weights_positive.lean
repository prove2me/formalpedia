-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalMomentSupport_weights_positive
-- name    : ThreeSum.TernaryPhysicalMomentSupport.weights_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:43.814938+00:00
-- url     : https://prove2.me/theorems/162c5c41-4cd8-4473-bd7e-488fd023df88
-- title:
--   Ternary Physical Moment Support: weights positive
-- statement:
--   The Ternary Physical Moment Support construction uses the weights positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L31-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalMomentSupport.lean#L31-L41

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

theorem ThreeSum.TernaryPhysicalMomentSupport.weights_positive (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    (i : Fin (support mode).card) : 0<weights mode mass i := by sorry
