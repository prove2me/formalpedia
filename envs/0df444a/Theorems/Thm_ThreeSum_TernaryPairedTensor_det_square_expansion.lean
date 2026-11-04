-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_det_square_expansion
-- name    : ThreeSum.TernaryPairedTensor.det_square_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:10.981652+00:00
-- url     : https://prove2.me/theorems/a21f833f-d1cd-4361-b5df-77b3cbf650b5
-- title:
--   Ternary Paired Tensor: det square expansion
-- statement:
--   The Ternary Paired Tensor construction uses the det square expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L36-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L36-L49

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.det_square_expansion {m : ℕ} (L R' : P → I → R)
    (e : Fin m → P) (cols : PairedIndex m → I) :
    (pairedMinor L R' e cols).det^2 =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)) *
        ∏ i : Fin m, L (e i) (cols (σ (.inl i))) * L (e i) (cols (τ (.inl i))) *
          R' (e i) (cols (σ (.inr i))) * R' (e i) (cols (τ (.inr i))) := by sorry
