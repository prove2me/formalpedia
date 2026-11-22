-- Prove2me | Theorems.Thm_QECCertificates_spanL_rowList_step
-- name    : QECCertificates.spanL_rowList_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:33.802803+00:00
-- url     : https://prove2.me/theorems/82f9a4f1-4b2e-4fd0-a1bd-3db77f1cb4fe
-- title:
--   QECCertificates: span L row List step
-- statement:
--   The QECCertificates construction uses the span L row List step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L233-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L233-L249

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_rowList_step (D : List (PivRow n)) (v : Vec n) :
    spanL (rowList (step D v)) = spanL (rowList D ++ [v]) := by sorry
