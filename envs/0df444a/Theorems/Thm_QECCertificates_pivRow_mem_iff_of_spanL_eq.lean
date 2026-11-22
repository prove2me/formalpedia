-- Prove2me | Theorems.Thm_QECCertificates_pivRow_mem_iff_of_spanL_eq
-- name    : QECCertificates.pivRow_mem_iff_of_spanL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:59.353862+00:00
-- url     : https://prove2.me/theorems/b4ac3be4-c98e-4718-b7cd-039928f0fde6
-- title:
--   QECCertificates: piv Row mem iff of span L eq
-- statement:
--   **Canonical form uniqueness**: two echelon mutually reduced row lists that span the same row
--       space
--   have the same set of rows.
--
--   Hence the output of `rowReduce` is a **canonical invariant** of the row space: two codes agree
--   exactly when the row sets of their elimination outputs agree (`rowReduce_mem_iff_of_spanL_eq`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L216-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Canonical.lean#L216-L300

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.pivRow_mem_iff_of_spanL_eq {D₁ D₂ : List (PivRow n)} (h₁ : IsEchelon D₁)
    (h₂ : IsEchelon D₂) (hspan : spanL (rowList D₁) = spanL (rowList D₂)) :
    ∀ x : PivRow n, x ∈ D₁ ↔ x ∈ D₂ := by sorry
