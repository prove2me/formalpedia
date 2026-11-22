-- Prove2me | Theorems.Thm_QECCertificates_LRAT_slotClauses_eq_none_none
-- name    : QECCertificates.LRAT.slotClauses_eq_none_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:22.103733+00:00
-- url     : https://prove2.me/theorems/223a27e7-1891-499c-903b-70c44fffa0a5
-- title:
--   LRAT: slot Clauses eq none none
-- statement:
--   The LRAT construction uses the slot Clauses eq none none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L546-L549
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L546-L549

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.slotClauses_eq_none_none {s : Nat → Nat → Option Nat} {i j x si : Nat}
    (ha : s (i - 1) j = none) (hb : s (i - 1) (j - 1) = none) (hs : s i j = some si) :
    slotClauses s i j x = [[(x, false), (si, true)], [(si, false), (x, true)]] := by sorry
