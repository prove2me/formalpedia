-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_echelonFrom
-- name    : QECCertificates.spanL_rowList_echelonFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:58.243741+00:00
-- url     : https://prove2.me/theorems/2a692506-3028-4921-9b27-abc3d410d6a6
-- title:
--   QECCertificates: span L row List echelon From
-- statement:
--   **Invariance of the row space**: the append-only echelon form spans the same row
--   space as the original list of rows, and so defines the same code.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L127-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L127-L130

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_echelonFrom (L : List (Vec n)) :
    spanL (rowList (echelonFrom L)) = spanL L := by sorry
