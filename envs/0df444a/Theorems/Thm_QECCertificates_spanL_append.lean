-- Prove2me | Theorems.Thm_QECCertificates_spanL_append
-- name    : QECCertificates.spanL_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:43.199987+00:00
-- url     : https://prove2.me/theorems/74a23d34-34ad-4b4a-aecf-0ef01a8978c3
-- title:
--   QECCertificates: span L append
-- statement:
--   The row space of an appended list is the supremum of the row spaces of the two
--   parts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L118-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L118-L121

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_append (A B : List (Vec n)) : spanL (A ++ B) = spanL A ⊔ spanL B := by sorry
