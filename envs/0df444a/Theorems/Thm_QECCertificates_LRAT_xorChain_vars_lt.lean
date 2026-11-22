-- Prove2me | Theorems.Thm_QECCertificates_LRAT_xorChain_vars_lt
-- name    : QECCertificates.LRAT.xorChain_vars_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:12.485163+00:00
-- url     : https://prove2.me/theorems/df2497fb-cae0-42c8-8428-ac2542ced2fc
-- title:
--   LRAT: xor Chain vars lt
-- statement:
--   The clause variables of a single chain all lie below the exit counter of its segment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1002-L1012
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L1002-L1012

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.xorChain_vars_lt {xs : List Nat} {w : Bool} {c : Nat} (hne : xs ≠ [])
    (hlt : ∀ t ∈ xs, t < c) :
    ∀ C ∈ (xorChain xs w c).1, ∀ l ∈ C, l.1 < (xorChain xs w c).2 := by sorry
