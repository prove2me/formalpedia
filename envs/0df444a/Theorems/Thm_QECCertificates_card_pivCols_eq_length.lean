-- Prove2me | Theorems.Thm_QECCertificates_card_pivCols_eq_length
-- name    : QECCertificates.card_pivCols_eq_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:42.864217+00:00
-- url     : https://prove2.me/theorems/5811cfcc-f858-40ac-9d09-0ab4d7ebb31c
-- title:
--   QECCertificates: card piv Cols eq length
-- statement:
--   Pairwise distinct pivot columns imply that the number of pivot columns equals the
--   number of rows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L178-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L178-L180

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}

theorem QECCertificates.card_pivCols_eq_length {D : List (PivRow n)} (h : NodupPiv D) :
    (pivCols D).card = D.length := by sorry
