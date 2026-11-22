-- Prove2me | Theorems.Thm_QECCertificates_LRAT_prod_sat
-- name    : QECCertificates.LRAT.prod_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:31.478472+00:00
-- url     : https://prove2.me/theorems/e408ea2b-cef6-4b50-9ab4-804e4ef00ddf
-- title:
--   LRAT: prod sat
-- statement:
--   The three clauses of the product block imply `a = x ∧ w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L445-L470
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L445-L470

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.prod_sat {σ : Assign} {a x w : Nat}
    (h1 : SatClause σ [(a, false), (x, true)])
    (h2 : SatClause σ [(a, false), (w, true)])
    (h3 : SatClause σ [(a, true), (x, false), (w, false)]) :
    σ a = (σ x && σ w) := by sorry
