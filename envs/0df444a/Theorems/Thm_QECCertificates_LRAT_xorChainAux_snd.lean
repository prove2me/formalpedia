-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChainAux_snd
-- name    : QECCertificates.LRAT.xorChainAux_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:44:36.800797+00:00
-- url     : https://prove2.me/theorems/a37ef35d-6aca-4317-8a16-9115537dc528
-- title:
--   LRAT: xor Chain Aux snd
-- statement:
--   The exit counter of a chain: one number is allocated per variable processed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L252-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L252-L261

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChainAux_snd : ∀ (rest : List Nat) (want : Bool) (cur c : Nat),
    (xorChainAux rest want cur c).2 = c + rest.length := by sorry
