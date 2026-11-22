-- Prove2me | Theorems.Thm_QECCertificates_kerVec_mem_kerL
-- name    : QECCertificates.kerVec_mem_kerL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:26.172121+00:00
-- url     : https://prove2.me/theorems/ecc4b88d-6e9a-4239-b6bb-dfb2ca97fcaf
-- title:
--   QECCertificates: ker Vec mem ker L
-- statement:
--   **Soundness direction**: a kernel vector really does lie in the kernel of these rows.
--
--   The proof cancels two sums: the dot product of `rk` with the kernel vector is expanded into
--   a double sum, the order of summation is exchanged, and the Kronecker form of (R1)/(R2)
--   collapses the inner sum to a single term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L189-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L189-L217

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerVec_mem_kerL {D : List (PivRow n)} (hD : IsReduced D) (j : Fin n) :
    kerVec D j ∈ kerL (rowList D) := by sorry
