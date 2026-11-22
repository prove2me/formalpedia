-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotBase_mono
-- name    : QECCertificates.LRAT.slotBase_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:02.915726+00:00
-- url     : https://prove2.me/theorems/a0bf6457-7f4f-4998-90a7-1c1997fe945c
-- title:
--   LRAT: slot Base mono
-- statement:
--   The slot base is monotone.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L437-L440
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L437-L440

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotBase_mono (k : Nat) {i i' : Nat} (h : i ≤ i') : slotBase k i ≤ slotBase k i' := by sorry
