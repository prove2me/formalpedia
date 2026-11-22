-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotBase_succ
-- name    : QECCertificates.LRAT.slotBase_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:43.685889+00:00
-- url     : https://prove2.me/theorems/14a24c6d-2bf0-4a76-b0b7-ac6db93d8492
-- title:
--   LRAT: slot Base succ
-- statement:
--   The block before row `i+1` has `min i (k + 1)` slots more than the block before row `i`,
--   namely those of row `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L432-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L432-L434

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotBase_succ (k i : Nat) : slotBase k (i + 1) = slotBase k i + min i (k + 1) := by sorry
