-- Prove2me | Theorems.Thm_QECCertificates_addSmul_cancel
-- name    : QECCertificates.addSmul_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:04.922586+00:00
-- url     : https://prove2.me/theorems/b25a4b39-c2a5-479b-b774-d65e4fd382a6
-- title:
--   QECCertificates: add Smul cancel
-- statement:
--   In characteristic 2 a row operation is invertible: adding and then adding back leaves
--   the row unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L222-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L222-L224

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.addSmul_cancel (v r : Vec n) (c : ZMod 2) : addSmul v r c + c • r = v := by sorry
