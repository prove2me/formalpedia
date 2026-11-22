-- Prove2me | Theorems.Thm_QECCertificates_LRAT_cntS_append
-- name    : QECCertificates.LRAT.cntS_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:32.369598+00:00
-- url     : https://prove2.me/theorems/c5a5b4ad-bbac-47c6-876f-e9a088d7a560
-- title:
--   LRAT: cnt S append
-- statement:
--   The LRAT construction uses the cnt S append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L68-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L68-L70

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.cntS_append (σ : Assign) (l₁ l₂ : List Nat) :
    cntS σ (l₁ ++ l₂) = cntS σ l₁ + cntS σ l₂ := by sorry
