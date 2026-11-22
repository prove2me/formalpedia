-- Prove2me | Theorems.Thm_QECCertificates_add_eq_zero_iff_eq
-- name    : QECCertificates.add_eq_zero_iff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:41.467803+00:00
-- url     : https://prove2.me/theorems/4f3f198c-3c0e-47ef-a68a-fa1a542c55cf
-- title:
--   QECCertificates: add eq zero iff eq
-- statement:
--   In characteristic 2, `a + b = 0 ↔ a = b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L68-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L68-L74

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by sorry
