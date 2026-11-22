-- Prove2me | Theorems.Thm_QECCertificates_kerVec_apply_free
-- name    : QECCertificates.kerVec_apply_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:33.298014+00:00
-- url     : https://prove2.me/theorems/878c81f1-c54f-4f80-88c2-aad4a1deb8d5
-- title:
--   QECCertificates: ker Vec apply free
-- statement:
--   On a free column the kernel vector is just `e_j`: every correction term
--   vanishes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L158-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L158-L164

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerVec_apply_free {D : List (PivRow n)} {j i : Fin n} (hi : IsFreeCol D i) :
    kerVec D j i = if i = j then 1 else 0 := by sorry
