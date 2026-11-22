-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_cons
-- name    : QECCertificates.LRAT.dotS_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:41:54.882796+00:00
-- url     : https://prove2.me/theorems/08b35b7d-4dfd-4d40-8a6e-8bc970111cb6
-- title:
--   LRAT: dot S cons
-- statement:
--   The LRAT construction uses the dot S cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L52-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L52-L53

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_cons (σ : Assign) (j : Nat) (s : List Nat) :
    dotS σ (j :: s) = (σ j ^^ dotS σ s) := by sorry

attribute [defeq] QECCertificates.LRAT.dotS_cons
