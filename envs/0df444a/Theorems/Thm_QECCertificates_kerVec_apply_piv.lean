-- Prove2me | Theorems.Thm_QECCertificates_kerVec_apply_piv
-- name    : QECCertificates.kerVec_apply_piv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:12.449635+00:00
-- url     : https://prove2.me/theorems/ce958264-8db2-4838-ac32-f1df3e0bbe63
-- title:
--   QECCertificates: ker Vec apply piv
-- statement:
--   On a pivot column the kernel vector reads off the corresponding entry of that
--   row.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L168-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L168-L182

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerVec_apply_piv {D : List (PivRow n)} (hD : IsReduced D) {j : Fin n} {rk : PivRow n}
    (hrk : rk ∈ D) :
    kerVec D j rk.2 = (if rk.2 = j then 1 else 0) + rk.1 j := by sorry
