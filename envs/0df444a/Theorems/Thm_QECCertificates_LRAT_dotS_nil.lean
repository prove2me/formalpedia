-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_nil
-- name    : QECCertificates.LRAT.dotS_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:54.554808+00:00
-- url     : https://prove2.me/theorems/03eef9cb-c505-468c-8e8f-05a7c53c08b3
-- title:
--   LRAT: dot S nil
-- statement:
--   The LRAT construction uses the dot S nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L50-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L50-L50

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_nil (σ : Assign) : dotS σ [] = false := by sorry

attribute [defeq] QECCertificates.LRAT.dotS_nil
