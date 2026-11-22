-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChainAux_vars_lt
-- name    : QECCertificates.LRAT.xorChainAux_vars_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:37.638645+00:00
-- url     : https://prove2.me/theorems/bf66e776-e575-4d23-aa19-648b31c820be
-- title:
--   LRAT: xor Chain Aux vars lt
-- statement:
--   The variable bound of the chain clauses: all of them lie below the exit counter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L274-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L274-L296

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChainAux_vars_lt : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    cur < c → (∀ t ∈ rest, t < c) →
    ∀ C ∈ (xorChainAux rest want cur c).1, ∀ l ∈ C, l.1 < c + rest.length := by sorry
