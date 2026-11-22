-- Prove2me | Theorems.Thm_QECCertificates_add_reduceAgainst_mem
-- name    : QECCertificates.add_reduceAgainst_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:09.926264+00:00
-- url     : https://prove2.me/theorems/53394932-277b-4a75-8beb-f69aac4e0643
-- title:
--   QECCertificates: add reduce Against mem
-- statement:
--   **Where the reduced part lands**: `v + reduceAgainst D v` is a linear combination of the row
--       vectors of `D`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L131-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RowReduce.lean#L131-L150

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.add_reduceAgainst_mem (D : List (PivRow n)) (v : Vec n) :
    v + reduceAgainst D v ∈ spanL (rowList D) := by sorry
