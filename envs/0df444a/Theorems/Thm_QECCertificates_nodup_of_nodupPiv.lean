-- Prove2me | Theorems.Thm_QECCertificates_nodup_of_nodupPiv
-- name    : QECCertificates.nodup_of_nodupPiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:28.674979+00:00
-- url     : https://prove2.me/theorems/34c8aa34-599a-4a67-8941-34fc0cd67f6b
-- title:
--   QECCertificates: nodup of nodup Piv
-- statement:
--   Pairwise distinct pivot columns imply pairwise distinct rows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L112-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L112-L127

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

theorem QECCertificates.nodup_of_nodupPiv (D : List (PivRow n)) :
    IsReduced D → NodupPiv D → D.Nodup := by sorry
