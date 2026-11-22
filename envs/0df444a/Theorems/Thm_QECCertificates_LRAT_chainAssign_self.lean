-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainAssign_self
-- name    : QECCertificates.LRAT.chainAssign_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:59.974795+00:00
-- url     : https://prove2.me/theorems/869c65dd-3cf2-46a8-97b3-c18793d08e76
-- title:
--   LRAT: chain Assign self
-- statement:
--   The value of `chainAssign` at the counter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L138-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L138-L141

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainAssign_self (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat) :
    chainAssign σ (x :: rest) acc c c = (acc ^^ σ x) := by sorry
