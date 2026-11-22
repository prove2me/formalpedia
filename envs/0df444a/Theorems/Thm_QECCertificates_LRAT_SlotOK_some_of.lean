-- Prove2me | Theorems.Thm_QECCertificates_LRAT_SlotOK_some_of
-- name    : QECCertificates.LRAT.SlotOK.some_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:18.83406+00:00
-- url     : https://prove2.me/theorems/8142f411-d13e-495c-ad40-7590bc15394b
-- title:
--   Slot OK: some of
-- statement:
--   The Slot OK construction uses the some of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L208-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L208-L213

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.SlotOK.some_of {s : Nat → Nat → Option Nat} {k : Nat} (hok : SlotOK s k) {i j : Nat}
    (h1 : 1 ≤ j) (h2 : j ≤ min i (k + 1)) : ∃ v, s i j = some v := by sorry
