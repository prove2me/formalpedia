-- Prove2me | Theorems.Thm_QECCertificates_LRAT_sat_two_of_imp
-- name    : QECCertificates.LRAT.sat_two_of_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:10.795907+00:00
-- url     : https://prove2.me/theorems/83c4d268-b133-4394-8acd-9aba6d0a13a3
-- title:
--   LRAT: sat two of imp
-- statement:
--   Binary clause `¬p ∨ q`: given by `bp = true → bq = true`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L476-L481
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L476-L481

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.sat_two_of_imp {τ : Assign} {p q : Nat} {bp bq : Bool}
    (hp : τ p = bp) (hq : τ q = bq) (h : bp = true → bq = true) :
    SatClause τ [(p, false), (q, true)] := by sorry
