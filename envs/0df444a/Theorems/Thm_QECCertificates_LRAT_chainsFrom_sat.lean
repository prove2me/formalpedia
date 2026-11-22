-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainsFrom_sat
-- name    : QECCertificates.LRAT.chainsFrom_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:35.282716+00:00
-- url     : https://prove2.me/theorems/1a63cffc-9b43-431c-9cc0-b47ac6d37227
-- title:
--   LRAT: chains From sat
-- statement:
--   The LRAT construction uses the chains From sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L496-L525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L496-L525

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainsFrom_sat {σ : Assign} {f : Nat → Nat} {rows : List (List Nat)}
    (hne : ∀ r ∈ rows, r ≠ []) :
    ∀ c, (∀ C ∈ (chainsFrom f rows c).1, SatClause σ C) →
      ∀ r ∈ rows, dotS (fun t => σ (f t)) r = false := by sorry
