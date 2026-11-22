-- Prove2me | Theorems.Thm_QECCertificates_spanL_singleton
-- name    : QECCertificates.spanL_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.256456+00:00
-- url     : https://prove2.me/theorems/8ca15590-9e57-4cb3-b3d9-5a0ac45d4947
-- title:
--   QECCertificates: span L singleton
-- statement:
--   The row space spanned by a single vector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L124-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L124-L129

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_singleton (v : Vec n) : spanL [v] = Submodule.span (ZMod 2) ({v} : Set (Vec n)) := by sorry
