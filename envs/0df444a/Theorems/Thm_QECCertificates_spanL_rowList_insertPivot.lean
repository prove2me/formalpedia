-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_insertPivot
-- name    : QECCertificates.spanL_rowList_insertPivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:27.351798+00:00
-- url     : https://prove2.me/theorems/95c3a404-3679-4c85-8fa3-6af6be4fdd17
-- title:
--   QECCertificates: span L row List insert Pivot
-- statement:
--   Insertion does not change the row space.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L184-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L184-L187

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    spanL (rowList (insertPivot D w p)) = spanL (rowList D ++ [w]) := by sorry
