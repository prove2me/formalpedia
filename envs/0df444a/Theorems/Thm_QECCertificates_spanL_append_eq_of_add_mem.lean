-- Prove2me | Theorems.Thm_QECCertificates_spanL_append_eq_of_add_mem
-- name    : QECCertificates.spanL_append_eq_of_add_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:52.626387+00:00
-- url     : https://prove2.me/theorems/1cba4f0e-597a-4734-9baf-f965d201d6d3
-- title:
--   QECCertificates: span L append eq of add mem
-- statement:
--   Equality of the row spaces, obtained from the previous statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L164-L180
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L164-L180

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_append_eq_of_add_mem {A : List (Vec n)} {v w : Vec n}
    (h : v + w ∈ spanL A) : spanL (A ++ [w]) = spanL (A ++ [v]) := by sorry
