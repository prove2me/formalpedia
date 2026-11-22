-- Prove2me | Theorems.Thm_QECCertificates_kerL_rowReduce
-- name    : QECCertificates.kerL_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:31.906026+00:00
-- url     : https://prove2.me/theorems/25f8c0e8-1ac3-4176-b771-60a7ab932365
-- title:
--   QECCertificates: ker L row Reduce
-- statement:
--   **Main theorem**: the kernel equals the space spanned by the kernel generators. The
--   list of rows is first put through the trusted row reduction, and the kernel generators are
--   read directly off the pivot structure that it outputs; the whole chain closes inside the
--   kernel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L391-L399
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L391-L399

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerL_rowReduce (L : List (Vec n)) :
    kerL L = spanL (kerBasis (rowReduce L)) := by sorry
