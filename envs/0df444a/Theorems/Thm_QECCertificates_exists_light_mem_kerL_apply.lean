-- Prove2me | Theorems.Thm_QECCertificates_exists_light_mem_kerL_apply
-- name    : QECCertificates.exists_light_mem_kerL_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:26.52012+00:00
-- url     : https://prove2.me/theorems/75e1cded-7553-45e7-8f57-8223e23f779c
-- title:
--   QECCertificates: exists light mem ker L apply
-- statement:
--   **The indexed form**: the kernel vector given by the free column `j` lies in the
--   kernel, has weight at most the rank plus one, and takes the value $1$ at `j`.
--
--   The clause "takes the value 1 at `j`" is needed for the frontier argument: the witness
--   construction for the hypergraph product requires the seed kernel vector to be nonzero at
--   some index (`s a₀ = 1` in `xwLeft`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L424-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L424-L434

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.exists_light_mem_kerL_apply (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    kerVec (rowReduce L) j ∈ kerL L
      ∧ hammingNorm (kerVec (rowReduce L) j) ≤ (rowReduce L).length + 1
      ∧ kerVec (rowReduce L) j j = 1 := by sorry
