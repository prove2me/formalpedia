-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorStepClauses_vars
-- name    : QECCertificates.LRAT.xorStepClauses_vars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:47.007694+00:00
-- url     : https://prove2.me/theorems/b9c6dcec-0528-40ac-b234-362bf840e5f5
-- title:
--   LRAT: xor Step Clauses vars
-- statement:
--   A variable in a step clause can only occupy one of three positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L264-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L264-L271

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorStepClauses_vars {cur x nxt : Nat} {C : Clause}
    (hC : C ∈ xorStepClauses cur x nxt) :
    ∀ l ∈ C, l.1 = cur ∨ l.1 = x ∨ l.1 = nxt := by sorry
