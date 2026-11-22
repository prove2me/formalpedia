-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotBase_pred
-- name    : QECCertificates.LRAT.slotBase_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:09.536135+00:00
-- url     : https://prove2.me/theorems/da64c945-32a3-46bd-891f-ca6a57037cab
-- title:
--   LRAT: slot Base pred
-- statement:
--   The "previous index" form of `slotBase`, with the hypothesis stated on the index
--   itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L444-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L444-L447

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotBase_pred {k i : Nat} (hi : 1 ≤ i) :
    slotBase k i = slotBase k (i - 1) + min (i - 1) (k + 1) := by sorry
