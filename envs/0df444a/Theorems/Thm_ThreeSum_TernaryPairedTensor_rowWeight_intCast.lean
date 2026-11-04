-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_rowWeight_intCast
-- name    : ThreeSum.TernaryPairedTensor.rowWeight_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:17.158306+00:00
-- url     : https://prove2.me/theorems/b1624935-a934-4b1c-bad7-2a7fb8681a06
-- title:
--   Ternary Paired Tensor: row Weight int Cast
-- statement:
--   The Ternary Paired Tensor construction uses the row Weight int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L77-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L77-L101

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.rowWeight_intCast {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) :
    (rowWeight A : ℤ) = ∑ cols : ι → Fin Λ, (Matrix.det (fun i j => A i (cols j)))^2 := by sorry
