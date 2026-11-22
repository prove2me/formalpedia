-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChain_sat
-- name    : QECCertificates.LRAT.xorChain_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:50.520952+00:00
-- url     : https://prove2.me/theorems/101355f0-3351-4226-9783-10ce05dde97f
-- title:
--   LRAT: xor Chain sat
-- statement:
--   Soundness of the chain (the nonempty form).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L182-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L182-L185

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChain_sat {σ : Assign} {x₀ : Nat} {rest : List Nat} {want : Bool} {start : Nat}
    (h : ∀ C ∈ (xorChainAux rest want x₀ start).1, SatClause σ C) :
    dotS σ (x₀ :: rest) = want := by sorry
