-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_det_row_expansion
-- name    : ThreeSum.TernaryPairedTensor.det_row_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:13.63848+00:00
-- url     : https://prove2.me/theorems/a65d602a-1061-4f73-9d42-7a15c2ca06ab
-- title:
--   Ternary Paired Tensor: det row expansion
-- statement:
--   The Ternary Paired Tensor construction uses the det row expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L24-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L24-L34

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.det_row_expansion {m : ℕ} (L R' : P → I → R)
    (e : Fin m → P) (cols : PairedIndex m → I) :
    (pairedMinor L R' e cols).det =
      ∑ σ : Equiv.Perm (PairedIndex m), ((Equiv.Perm.sign σ : ℤ) : R) *
        (∏ i : Fin m, L (e i) (cols (σ (.inl i)))) *
        (∏ i : Fin m, R' (e i) (cols (σ (.inr i)))) := by sorry
