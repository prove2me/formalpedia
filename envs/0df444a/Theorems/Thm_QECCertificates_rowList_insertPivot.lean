-- Prove2me | Theorems.Thm_QECCertificates_rowList_insertPivot
-- name    : QECCertificates.rowList_insertPivot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:19.730694+00:00
-- url     : https://prove2.me/theorems/604c3313-6dd5-47cb-a135-9d0b3902fb74
-- title:
--   QECCertificates: row List insert Pivot
-- statement:
--   The QECCertificates construction uses the row List insert Pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L179-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L179-L181

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.rowList_insertPivot (D : List (PivRow n)) (w : Vec n) (p : Fin n) :
    rowList (insertPivot D w p) = (rowList D).map (fun r => r + (r p) • w) ++ [w] := by sorry
