-- Prove2me | Theorems.Thm_QECCertificates_finrank_spanL_eq_length_rowReduce
-- name    : QECCertificates.finrank_spanL_eq_length_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:42.186278+00:00
-- url     : https://prove2.me/theorems/b01fc884-d596-431c-b792-e80ddb7f8e7c
-- title:
--   QECCertificates: finrank span L eq length row Reduce
-- statement:
--   **Rank certificate (main theorem)**: the dimension of the space spanned by the list of
--   rows equals the number of rows of the row-reduction output.
--
--   The list of pivot rows produced by the reduction is itself the certificate: the kernel only
--   has to count the rows and check `IsReduced` to verify the rank independently, with no need
--   to trust any external script.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L201-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L201-L204

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

theorem QECCertificates.finrank_spanL_eq_length_rowReduce (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (rowReduce L).length := by sorry
