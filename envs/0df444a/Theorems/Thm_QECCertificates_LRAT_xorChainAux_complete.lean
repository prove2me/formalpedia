-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChainAux_complete
-- name    : QECCertificates.LRAT.xorChainAux_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:01.61352+00:00
-- url     : https://prove2.me/theorems/61832241-0c6d-4e1b-ba70-86978359df96
-- title:
--   LRAT: xor Chain Aux complete
-- statement:
--   **Completeness of a chain**: if the semantic condition holds and every input variable
--   read by the chain lies below the counter `c`, then `chainAssign` satisfies all the clauses
--   of the chain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L192-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L192-L238

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChainAux_complete : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    cur < c → (∀ t ∈ rest, t < c) → dotS σ (cur :: rest) = want →
    ∀ C ∈ (xorChainAux rest want cur c).1, SatClause (chainAssign σ rest (σ cur) c) C := by sorry
