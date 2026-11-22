-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainFill_cons
-- name    : QECCertificates.LRAT.chainFill_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:47:29.464011+00:00
-- url     : https://prove2.me/theorems/7b02371a-efb5-4edf-93b6-f74f0f4865f4
-- title:
--   LRAT: chain Fill cons
-- statement:
--   The LRAT construction uses the chain Fill cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L74-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L74-L76

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainFill_cons (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat) :
    chainFill σ (x :: rest) acc c t =
      (if t = c then (acc ^^ σ x) else chainFill σ rest (acc ^^ σ x) (c + 1) t) := by sorry
