-- Prove2me | Theorems.Thm_QECCertificates_LRAT_prodClauses_vars_lt
-- name    : QECCertificates.LRAT.prodClauses_vars_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:08.459071+00:00
-- url     : https://prove2.me/theorems/bc69f529-9b83-4e8e-8e8c-b735b2efdb7d
-- title:
--   LRAT: prod Clauses vars lt
-- statement:
--   The variables of the product-block clauses all lie below `c + n` (and when `n ≤ c` the
--   input variables are among them).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L991-L999
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L991-L999

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.prodClauses_vars_lt {c n : Nat} (hc : n ≤ c) :
    ∀ C ∈ prodClauses c n, ∀ l ∈ C, l.1 < c + n := by sorry
