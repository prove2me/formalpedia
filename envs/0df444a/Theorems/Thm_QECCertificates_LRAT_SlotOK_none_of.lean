-- Prove2me | Theorems.Thm_QECCertificates_LRAT_SlotOK_none_of
-- name    : QECCertificates.LRAT.SlotOK.none_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:21.445433+00:00
-- url     : https://prove2.me/theorems/371579bb-eabe-4fac-9c83-dd256c6af7ad
-- title:
--   Slot OK: none of
-- statement:
--   The Slot OK construction uses the none of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L215-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L215-L216

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.SlotOK.none_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h : ¬(1 ≤ j ∧ j ≤ min i (k + 1))) : s i j = none := by sorry
