-- Prove2me | Theorems.Thm_QECCertificates_isReduced_rowReduce
-- name    : QECCertificates.isReduced_rowReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:21.808264+00:00
-- url     : https://prove2.me/theorems/5df7ca9e-550a-4e67-981d-a0ca1477cf59
-- title:
--   QECCertificates: is Reduced row Reduce
-- statement:
--   **The output is mutually reduced**: the result is a set of pivot rows, each of them 1 at its
--       own pivot column and 0 at the others.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L297-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L297-L298

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.isReduced_rowReduce (L : List (Vec n)) : IsReduced (rowReduce L) := by sorry
