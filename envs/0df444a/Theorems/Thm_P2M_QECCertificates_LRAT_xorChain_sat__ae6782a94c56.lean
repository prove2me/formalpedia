-- Prove2me | Theorems.Thm_P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56
-- name    : P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:14.77691+00:00
-- url     : https://prove2.me/theorems/75c78709-bf41-4b05-9ef0-e3a3b2febc68
-- title:
--   P2 M QECCertificates LRAT xor Chain sat  ae6782a94c56: P2 M QECCertificates LRAT xor Chain sat  ae6782a94c56
-- statement:
--   Soundness of the chain for an arbitrary nonempty list of variables; used when a
--   definition such as `prodVars` does not reduce syntactically.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L189-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L189-L194

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56 {σ : Assign} {xs : List Nat} {want : Bool} {start : Nat}
    (hne : xs ≠ []) (h : ∀ C ∈ (xorChain xs want start).1, SatClause σ C) :
    dotS σ xs = want := by sorry

alias «QECCertificates».«LRAT».«xorChain_sat'» := P2M_QECCertificates_LRAT_xorChain_sat__ae6782a94c56
