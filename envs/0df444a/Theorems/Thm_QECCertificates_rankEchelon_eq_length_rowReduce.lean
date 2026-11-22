-- Prove2me | Theorems.Thm_QECCertificates_rankEchelon_eq_length_rowReduce
-- name    : QECCertificates.rankEchelon_eq_length_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:03.814463+00:00
-- url     : https://prove2.me/theorems/b68aefdb-a785-4754-ad41-4ae606668b62
-- title:
--   QECCertificates: rank Echelon eq length row Reduce
-- statement:
--   **The bridge theorem**: the append-only echelon form and `rowReduce` give the same
--   rank.
--
--   Both are outputs of the same greedy pivot count, with the same row space, and in both cases
--   the number of rows is the rank. Downstream rank and `k` claims can therefore **switch
--   backends** without any change to the mathematics; `rowReduce` and its downstream users
--   (canonical-form uniqueness in `GF2/Canonical.lean` relies on the RREF produced by
--   back-substitution) are untouched.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L356-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L356-L359

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.rankEchelon_eq_length_rowReduce (L : List (Vec n)) :
    rankEchelon L = (rowReduce L).length := by sorry
