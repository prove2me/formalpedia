-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowReduce
-- name    : QECCertificates.spanL_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:08.882803+00:00
-- url     : https://prove2.me/theorems/548ded24-f5ff-45c1-b2bb-0e8e0c69a34c
-- title:
--   QECCertificates: span L row Reduce
-- statement:
--   **The row space is unchanged**: elimination does not change the row space, hence does not
--       change the code it defines.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L291-L293
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L291-L293

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowReduce (L : List (Vec n)) : spanL (rowList (rowReduce L)) = spanL L := by sorry
