-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorStep_sat
-- name    : QECCertificates.LRAT.xorStep_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:06.124798+00:00
-- url     : https://prove2.me/theorems/d752c1be-29ca-4557-bb7e-a49d1634af5b
-- title:
--   LRAT: xor Step sat
-- statement:
--   Soundness of one step: all four clauses true implies that `nxt` takes the value
--   `cur ⊕ x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L118-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L118-L133

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorStep_sat {σ : Assign} {cur x nxt : Nat}
    (h : ∀ C ∈ xorStepClauses cur x nxt, SatClause σ C) :
    σ nxt = (σ cur ^^ σ x) := by sorry
