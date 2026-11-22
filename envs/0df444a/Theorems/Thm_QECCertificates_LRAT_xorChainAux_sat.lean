-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChainAux_sat
-- name    : QECCertificates.LRAT.xorChainAux_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:09.685115+00:00
-- url     : https://prove2.me/theorems/7caedf07-ba89-4093-9f61-cd6d4f629e0c
-- title:
--   LRAT: xor Chain Aux sat
-- statement:
--   Soundness of the chain: all clauses true implies `dotS σ (cur :: rest) = want`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L147-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L147-L171

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChainAux_sat : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    (∀ C ∈ (xorChainAux rest want cur c).1, SatClause σ C) →
    dotS σ (cur :: rest) = want := by sorry
