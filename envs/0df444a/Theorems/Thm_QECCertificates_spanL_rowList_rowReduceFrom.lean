-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_rowReduceFrom
-- name    : QECCertificates.spanL_rowList_rowReduceFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.56071+00:00
-- url     : https://prove2.me/theorems/1075574f-f4c6-4946-8ff1-f4168f19a616
-- title:
--   QECCertificates: span L row List row Reduce From
-- statement:
--   The QECCertificates construction uses the span L row List row Reduce From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L270-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L270-L278

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_rowReduceFrom (D : List (PivRow n)) (rest : List (Vec n)) :
    spanL (rowList (rowReduceFrom D rest)) = spanL (rowList D ++ rest) := by sorry
