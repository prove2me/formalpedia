-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedTensor_tuple_sum_tensor_expansion
-- name    : ThreeSum.TernaryPairedTensor.tuple_sum_tensor_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:18.522712+00:00
-- url     : https://prove2.me/theorems/a55ab8cd-9a2c-41e1-9a86-59292b6f328f
-- title:
--   Ternary Paired Tensor: tuple sum tensor expansion
-- statement:
--   The tuple sum is a product of fourth mixed tensor entries. Thus no
--   enumeration of all ordered `m`-tuples is required to compute this score.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L53-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean#L53-L71

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]

theorem ThreeSum.TernaryPairedTensor.tuple_sum_tensor_expansion {m : ℕ} (L R' : P → I → R)
    (cols : PairedIndex m → I) :
    (∑ e : Fin m → P, (pairedMinor L R' e cols).det^2) =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by sorry
