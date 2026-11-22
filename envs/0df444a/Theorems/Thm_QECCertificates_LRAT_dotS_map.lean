-- Prove2me | Theorems.Thm_QECCertificates_LRAT_dotS_map
-- name    : QECCertificates.LRAT.dotS_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:43:47.048808+00:00
-- url     : https://prove2.me/theorems/016d3079-e008-4208-a309-af62668677af
-- title:
--   LRAT: dot S map
-- statement:
--   The LRAT construction uses the dot S map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L416-L420
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Encode.lean#L416-L420

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.dotS_map (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    dotS σ (l.map f) = dotS (fun t => σ (f t)) l := by sorry
