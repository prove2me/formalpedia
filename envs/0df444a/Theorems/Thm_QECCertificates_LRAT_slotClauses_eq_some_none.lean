-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_some_none
-- name    : QECCertificates.LRAT.slotClauses_eq_some_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:18.253726+00:00
-- url     : https://prove2.me/theorems/101a34c2-680e-4495-a00b-69e14e6a7abf
-- title:
--   LRAT: slot Clauses eq some none
-- statement:
--   The LRAT construction uses the slot Clauses eq some none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L532-L537
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L532-L537

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotClauses_eq_some_none {s : Nat → Nat → Option Nat} {i j x a si : Nat}
    (ha : s (i - 1) j = some a) (hb : s (i - 1) (j - 1) = none) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(a, false), (si, true)], [(x, false), (si, true)],
       [(si, false), (a, true), (x, true)]] := by sorry
