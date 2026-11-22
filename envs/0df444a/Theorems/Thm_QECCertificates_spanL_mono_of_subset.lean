-- Prove2me | Theorems.Thm_QECCertificates_spanL_mono_of_subset
-- name    : QECCertificates.spanL_mono_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:53.57579+00:00
-- url     : https://prove2.me/theorems/b11543a3-5a97-48f7-8e25-41ab94e1d733
-- title:
--   QECCertificates: span L mono of subset
-- statement:
--   The row space is monotone with respect to inclusion of lists.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L138-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L138-L139

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_mono_of_subset {A B : List (Vec n)} (h : A ⊆ B) : spanL A ≤ spanL B := by sorry
