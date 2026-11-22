-- Prove2me | Theorems.Thm_QECCertificates_kerL_eq_of_spanL_eq
-- name    : QECCertificates.kerL_eq_of_spanL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:32.342676+00:00
-- url     : https://prove2.me/theorems/12600cbc-1466-4ec5-afcb-3b40059ff61b
-- title:
--   QECCertificates: ker L eq of span L eq
-- statement:
--   The kernel depends only on the row space: two lists of rows with the same row space
--   give the same kernel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L112-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L112-L122

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.kerL_eq_of_spanL_eq {A B : List (Vec n)} (h : spanL A = spanL B) : kerL A = kerL B := by sorry
