-- Prove2me | Theorems.Thm_QECCertificates_reduceAgainst_eq_zero_of_rows_zero
-- name    : QECCertificates.reduceAgainst_eq_zero_of_rows_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:18.146275+00:00
-- url     : https://prove2.me/theorems/104b67d7-638b-44a9-bbc6-06a461464ba1
-- title:
--   QECCertificates: reduce Against eq zero of rows zero
-- statement:
--   If every row of `D` is 0 at column `q` and `v q = 0`, then the reduced vector is still 0 at
--       position `q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L92-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L92-L102

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.reduceAgainst_eq_zero_of_rows_zero {D : List (PivRow n)} {q : Fin n} {v : Vec n}
    (hrows : ∀ ri ∈ D, ri.1 q = 0) (hv : v q = 0) : reduceAgainst D v q = 0 := by sorry
