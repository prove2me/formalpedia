-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_none_some
-- name    : QECCertificates.LRAT.slotClauses_eq_none_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:18.997803+00:00
-- url     : https://prove2.me/theorems/ebba1fc9-67dc-4094-9c76-e49a8124fd23
-- title:
--   LRAT: slot Clauses eq none some
-- statement:
--   The LRAT construction uses the slot Clauses eq none some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L539-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L539-L544

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotClauses_eq_none_some {s : Nat → Nat → Option Nat} {i j x b si : Nat}
    (ha : s (i - 1) j = none) (hb : s (i - 1) (j - 1) = some b) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(b, false), (x, false), (si, true)], [(si, false), (x, true)],
       [(si, false), (b, true)]] := by sorry
