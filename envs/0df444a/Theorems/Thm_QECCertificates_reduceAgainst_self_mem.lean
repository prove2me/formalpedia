-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_self_mem
-- name    : QECCertificates.reduceAgainst_self_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:20.48595+00:00
-- url     : https://prove2.me/theorems/8379882e-5586-4a25-82b7-ba9335484346
-- title:
--   QECCertificates: reduce Against self mem
-- statement:
--   **The reduction vanishes on the generators**: for a mutually reduced set of pivot
--   rows, eliminating a row by the set itself sends that row to zero.
--
--   This is the precise form of idempotence for row reduction: when the process reaches a
--   row's own pivot column the row is annihilated outright, and no later row can disturb that
--   column again, because (R2) keeps every other row zero there.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L104-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L104-L122

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_self_mem {D : List (PivRow n)} (hD : IsReduced D) {ri : PivRow n}
    (hri : ri ∈ D) : reduceAgainst D ri.1 = 0 := by sorry
