-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainAssign_succ
-- name    : QECCertificates.LRAT.chainAssign_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:43.377951+00:00
-- url     : https://prove2.me/theorems/b6332168-1178-4809-aec4-f796c8692fa3
-- title:
--   LRAT: chain Assign succ
-- statement:
--   One step past the counter (the `chainAssign` version).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L128-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L128-L135

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainAssign_succ (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat)
    (h : c < t) :
    chainAssign σ (x :: rest) acc c t = chainAssign σ rest (acc ^^ σ x) (c + 1) t := by sorry
