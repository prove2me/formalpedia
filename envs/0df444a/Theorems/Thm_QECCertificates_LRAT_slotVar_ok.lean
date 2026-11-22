-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotVar_ok
-- name    : QECCertificates.LRAT.slotVar_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:36.141847+00:00
-- url     : https://prove2.me/theorems/84683bf3-ca32-4e55-b554-18a4198affcf
-- title:
--   LRAT: slot Var ok
-- statement:
--   The LRAT construction uses the slot Var ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L536-L538
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L536-L538

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotVar_ok (c k : Nat) : SlotOK (slotVar c k) k := by sorry
