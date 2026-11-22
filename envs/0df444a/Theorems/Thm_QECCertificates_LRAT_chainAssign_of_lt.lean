-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
-- name    : QECCertificates.LRAT.chainAssign_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:28.182834+00:00
-- url     : https://prove2.me/theorems/4c1354dc-e707-49bc-b1a8-c30cbcbbf0a7
-- title:
--   LRAT: chain Assign of lt
-- statement:
--   The LRAT construction uses the chain Assign of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L123-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L123-L125

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainAssign_of_lt {σ : Assign} {rest : List Nat} {acc : Bool} {c t : Nat}
    (h : t < c) : chainAssign σ rest acc c t = σ t := by sorry
