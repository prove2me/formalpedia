-- Prove2me | Theorems.Thm_QECCertificates_LRAT_satFormula_append
-- name    : QECCertificates.LRAT.satFormula_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:53.109238+00:00
-- url     : https://prove2.me/theorems/53ced774-2963-43c6-836d-56a3768fef45
-- title:
--   LRAT: sat Formula append
-- statement:
--   The LRAT construction uses the sat Formula append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L400-L409
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L400-L409

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.satFormula_append {σ : Assign} {A B : CNF} :
    SatFormula σ (A ++ B) ↔ SatFormula σ A ∧ SatFormula σ B := by sorry
