-- Prove2me | Theorems.Thm_QECCertificates_mem_support
-- name    : QECCertificates.mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:54.409809+00:00
-- url     : https://prove2.me/theorems/437a4893-74b7-4d96-8db2-8f91b53f57ff
-- title:
--   QECCertificates: mem support
-- statement:
--   The QECCertificates construction uses the mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L79-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L79-L80

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_support {v : Vec n} {i : Fin n} : i ∈ support v ↔ v i ≠ 0 := by sorry
