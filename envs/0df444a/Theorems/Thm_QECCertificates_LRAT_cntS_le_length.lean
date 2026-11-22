-- Prove2me | Theorems.Thm_QECCertificates_LRAT_cntS_le_length
-- name    : QECCertificates.LRAT.cntS_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:46.520562+00:00
-- url     : https://prove2.me/theorems/fbe31786-319e-48a6-a499-33c9d5784c4c
-- title:
--   LRAT: cnt S le length
-- statement:
--   The LRAT construction uses the cnt S le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L78-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L78-L79

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.cntS_le_length (σ : Assign) (l : List Nat) : cntS σ l ≤ l.length := by sorry
