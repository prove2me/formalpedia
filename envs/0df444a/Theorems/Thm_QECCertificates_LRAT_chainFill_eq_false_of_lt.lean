-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainFill_eq_false_of_lt
-- name    : QECCertificates.LRAT.chainFill_eq_false_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:32.754422+00:00
-- url     : https://prove2.me/theorems/85e151ff-5d38-4e66-b073-71afa11da8c3
-- title:
--   LRAT: chain Fill eq false of lt
-- statement:
--   Below the counter the input is not read: the fill value is always `false`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L91-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L91-L98

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainFill_eq_false_of_lt (σ : Assign) (rest : List Nat) (acc : Bool) (c : Nat) :
    ∀ t, t < c → chainFill σ rest acc c t = false := by sorry
