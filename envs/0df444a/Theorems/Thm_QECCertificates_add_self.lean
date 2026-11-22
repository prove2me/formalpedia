-- Prove2me | Theorems.Thm_QECCertificates_add_self
-- name    : QECCertificates.add_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:51.733297+00:00
-- url     : https://prove2.me/theorems/eb9bc1d4-b9cb-41b7-b976-551042023b8c
-- title:
--   QECCertificates: add self
-- statement:
--   Characteristic 2: a vector over GF(2) added to itself is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L88-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L88-L89

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.add_self (v : Vec n) : v + v = 0 := by sorry
