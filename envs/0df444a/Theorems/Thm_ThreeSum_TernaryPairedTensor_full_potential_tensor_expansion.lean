-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_full_potential_tensor_expansion
-- name    : ThreeSum.TernaryPairedTensor.full_potential_tensor_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:36.244432+00:00
-- url     : https://prove2.me/theorems/f0921d08-e1d8-4a87-b13f-88b991380e51
-- title:
--   Ternary Paired Tensor: full potential tensor expansion
-- statement:
--   The exact natural potential cast to integers is computed by fourth mixed
--   channels followed by a fixed-degree polynomial in those channel values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L105-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L105-L116

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.full_potential_tensor_expansion {m Λ : ℕ} (L R' : P → Fin Λ → ℤ) :
    ((∑ e : Fin m → P, rowWeight (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) =
      ∑ cols : PairedIndex m → Fin Λ,
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : ℤ) * ((Equiv.Perm.sign τ : ℤ) : ℤ)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by sorry
