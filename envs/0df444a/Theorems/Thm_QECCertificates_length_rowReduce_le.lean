-- Prove2me | Theorems.Thm_QECCertificates_length_rowReduce_le
-- name    : QECCertificates.length_rowReduce_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:07.931274+00:00
-- url     : https://prove2.me/theorems/3123562b-b16e-4532-9123-da9d04c8b5a6
-- title:
--   QECCertificates: length row Reduce le
-- statement:
--   The rank is at most the length of the encoding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L207-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L207-L210

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

theorem QECCertificates.length_rowReduce_le (L : List (Vec n)) : (rowReduce L).length ≤ n := by sorry
