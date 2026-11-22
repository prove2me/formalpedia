-- Prove2me | Theorems.Thm_QECCertificates_LRAT_sat_three_of_imp2
-- name    : QECCertificates.LRAT.sat_three_of_imp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:12.284198+00:00
-- url     : https://prove2.me/theorems/29e83e53-7f88-45e7-a14e-624532a11996
-- title:
--   LRAT: sat three of imp2
-- statement:
--   Ternary clause `¬s ∨ a ∨ x`: given by `(s ∧ ¬a) → x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L496-L505
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L496-L505

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.sat_three_of_imp2 {τ : Assign} {s a x : Nat} {bs ba bx : Bool}
    (hs : τ s = bs) (ha : τ a = ba) (hx : τ x = bx)
    (h : bs = true → ba = false → bx = true) :
    SatClause τ [(s, false), (a, true), (x, true)] := by sorry
