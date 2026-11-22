-- Prove2me | Theorems.Thm_QECCertificates_LRAT_sat_three_of_imp
-- name    : QECCertificates.LRAT.sat_three_of_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:10.745106+00:00
-- url     : https://prove2.me/theorems/5ca6be9a-3b07-4539-9b63-8f43ecff368e
-- title:
--   LRAT: sat three of imp
-- statement:
--   Ternary clause `¬a ∨ ¬x ∨ s`: given by `(a ∧ x) → s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L484-L493
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L484-L493

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.sat_three_of_imp {τ : Assign} {a x s : Nat} {ba bx bs : Bool}
    (ha : τ a = ba) (hx : τ x = bx) (hs : τ s = bs)
    (h : ba = true → bx = true → bs = true) :
    SatClause τ [(a, false), (x, false), (s, true)] := by sorry
