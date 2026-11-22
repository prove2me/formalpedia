-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_cons
-- name    : QECCertificates.reduceAgainst_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:08.868988+00:00
-- url     : https://prove2.me/theorems/a59d0b18-a0c0-4c6c-9baa-df7b037209f1
-- title:
--   QECCertificates: reduce Against cons
-- statement:
--   The QECCertificates construction uses the reduce Against cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L86-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L86-L88

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_cons (ri : PivRow n) (D : List (PivRow n)) (v : Vec n) :
    reduceAgainst (ri :: D) v = reduceAgainst D (v + (v ri.2) • ri.1) := by sorry
