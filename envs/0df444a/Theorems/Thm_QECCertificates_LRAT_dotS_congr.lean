-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_congr
-- name    : QECCertificates.LRAT.dotS_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:46.377626+00:00
-- url     : https://prove2.me/theorems/4596e464-4ffa-4c31-89b6-93d6befcdc03
-- title:
--   LRAT: dot S congr
-- statement:
--   The LRAT construction uses the dot S congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L422-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L422-L429

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_congr {σ τ : Assign} {l : List Nat} (h : ∀ j ∈ l, σ j = τ j) :
    dotS σ l = dotS τ l := by sorry
