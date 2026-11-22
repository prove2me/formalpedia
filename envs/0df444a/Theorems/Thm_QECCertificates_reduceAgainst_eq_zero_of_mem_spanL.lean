-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_eq_zero_of_mem_spanL
-- name    : QECCertificates.reduceAgainst_eq_zero_of_mem_spanL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:22.868011+00:00
-- url     : https://prove2.me/theorems/0a8b7bc5-1c71-4c0d-a112-0b38534edb4a
-- title:
--   QECCertificates: reduce Against eq zero of mem span L
-- statement:
--   **The reduction vanishes exactly on the row space**: when `D` is mutually reduced,
--   `reduceAgainst D` annihilates `spanL (rowList D)`.
--
--   The proof is the standard argument that linearity plus vanishing on the generators gives
--   vanishing on the whole span: `spanL (rowList D)` is spanned by `rowList D`, on which
--   `reduceAgainst D` vanishes, so `spanL (rowList D)` is contained in
--   `comap (reduceAgainstLin D) ⊥`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L131-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L131-L142

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

theorem QECCertificates.reduceAgainst_eq_zero_of_mem_spanL {D : List (PivRow n)} (hD : IsReduced D) {v : Vec n}
    (hv : v ∈ spanL (rowList D)) : reduceAgainst D v = 0 := by sorry
