-- Prove2me | Theorems.Thm_QECCertificates_LRAT_certAssign_lt
-- name    : QECCertificates.LRAT.certAssign_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:08.520374+00:00
-- url     : https://prove2.me/theorems/d2cfba59-bd7f-41ae-bdf9-ebc268e3130d
-- title:
--   LRAT: cert Assign lt
-- statement:
--   The LRAT construction uses the cert Assign lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L186-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Distance.lean#L186-L189

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.certAssign_lt {n : ℕ} (E w : Vec n) {t : ℕ} (ht : t < n) :
    certAssign n E w t = decide (E ⟨t, ht⟩ = 1) := by sorry
