-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_minorWeight_intCast
-- name    : ThreeSum.TernaryPairedTensor.minorWeight_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:13.307148+00:00
-- url     : https://prove2.me/theorems/f6e99847-3425-405f-9573-17d4fdaee80b
-- title:
--   Ternary Paired Tensor: minor Weight int Cast
-- statement:
--   The Ternary Paired Tensor construction uses the minor Weight int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L73-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L73-L75

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.minorWeight_intCast {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) :
    (minorWeight A : ℤ) = ∑ f : Fin d → Fin Λ, (A.submatrix id f).det^2 := by sorry
