-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainAssign_congr
-- name    : QECCertificates.LRAT.chainAssign_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:48.359805+00:00
-- url     : https://prove2.me/theorems/eaef86eb-3548-43b4-b2df-c24d24f6b927
-- title:
--   LRAT: chain Assign congr
-- statement:
--   Compatibility of `chainAssign`: if the two assignments agree below the counter according
--   to `hlt` and on `rest` according to `h`, then they are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L145-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L145-L153

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainAssign_congr {σ σ' : Assign} {rest : List Nat} {acc acc' : Bool} {c : Nat}
    (hacc : acc = acc') (hlt : ∀ t, t < c → σ t = σ' t) (h : ∀ t ∈ rest, σ t = σ' t) :
    ∀ t, chainAssign σ rest acc c t = chainAssign σ' rest acc' c t := by sorry
