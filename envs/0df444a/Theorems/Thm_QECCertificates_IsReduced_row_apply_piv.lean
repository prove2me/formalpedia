-- Prove2me | Theorems.Thm_QECCertificates_IsReduced_row_apply_piv
-- name    : QECCertificates.IsReduced.row_apply_piv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:09.852523+00:00
-- url     : https://prove2.me/theorems/619ef6fe-9a0a-4770-bbf6-1d3cba6e6ab8
-- title:
--   Is Reduced: row apply piv
-- statement:
--   The paired form of (R2): the entry of any pivot row at any pivot column is of
--   Kronecker type.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L138-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L138-L143

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.IsReduced.row_apply_piv {D : List (PivRow n)} (hD : IsReduced D)
    {ri rj : PivRow n} (hri : ri ∈ D) (hrj : rj ∈ D) :
    ri.1 rj.2 = if ri = rj then 1 else 0 := by sorry
