-- Prove2me | Theorems.Thm_QECCertificates_rowList_insertPivotA
-- name    : QECCertificates.rowList_insertPivotA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:31.346789+00:00
-- url     : https://prove2.me/theorems/73f40ba8-d3a9-4939-bc82-f9d81b5aa9d1
-- title:
--   QECCertificates: row List insert Pivot A
-- statement:
--   The QECCertificates construction uses the row List insert Pivot A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L85-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L85-L87

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.rowList_insertPivotA (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivotA D w p) = rowList D ++ [w] := by sorry
