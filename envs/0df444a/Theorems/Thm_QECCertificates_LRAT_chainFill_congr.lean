-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainFill_congr
-- name    : QECCertificates.LRAT.chainFill_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:59.954795+00:00
-- url     : https://prove2.me/theorems/2385ed63-764f-4568-a813-50fd6654c676
-- title:
--   LRAT: chain Fill congr
-- statement:
--   The fill value reads only the elements of `rest` and the initial accumulator; the
--   compatibility needed for concatenation rests on this.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L102-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L102-L116

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainFill_congr {σ σ' : Assign} (rest : List Nat) (acc acc' : Bool) (c : Nat)
    (hacc : acc = acc') (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainFill σ rest acc c t = chainFill σ' rest acc' c t := by sorry
