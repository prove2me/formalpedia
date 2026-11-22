-- Prove2me | Theorems.Thm_QECCertificates_spanL_append_singleton
-- name    : QECCertificates.spanL_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:44.954731+00:00
-- url     : https://prove2.me/theorems/7ebfe63b-6801-481c-980e-8ef314245a54
-- title:
--   QECCertificates: span L append singleton
-- statement:
--   The single-row version: the row space after appending one row is the supremum of the
--   original row space and that row.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L133-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L133-L135

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_append_singleton (A : List (Vec n)) (v : Vec n) :
    spanL (A ++ [v]) = spanL A ⊔ Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by sorry
