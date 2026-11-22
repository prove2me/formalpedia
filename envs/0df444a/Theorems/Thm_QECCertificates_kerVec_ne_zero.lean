-- Prove2me | Theorems.Thm_QECCertificates_kerVec_ne_zero
-- name    : QECCertificates.kerVec_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:50.88901+00:00
-- url     : https://prove2.me/theorems/8f72e1f1-48c7-4c8b-b9c3-96844bcc9a1e
-- title:
--   QECCertificates: ker Vec ne zero
-- statement:
--   **A kernel vector is nonzero**: on a free column it is just `e_j`, so it cannot be the
--   zero vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L223-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L223-L229

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerVec_ne_zero {D : List (PivRow n)} {j : Fin n} (hj : IsFreeCol D j) :
    kerVec D j ≠ 0 := by sorry
