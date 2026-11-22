-- Prove2me | Theorems.Thm_QECCertificates_nodupPiv_rowReduce
-- name    : QECCertificates.nodupPiv_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:49.555296+00:00
-- url     : https://prove2.me/theorems/d8c0c774-0063-48a3-b119-0df981b49148
-- title:
--   QECCertificates: nodup Piv row Reduce
-- statement:
--   The pivot columns of the output of `rowReduce` are pairwise distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L101-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L101-L102

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

theorem QECCertificates.nodupPiv_rowReduce (L : List (Vec n)) : NodupPiv (rowReduce L) := by sorry
