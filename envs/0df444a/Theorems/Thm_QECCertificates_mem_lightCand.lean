-- Prove2me | Theorems.Thm_QECCertificates_mem_lightCand
-- name    : QECCertificates.mem_lightCand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:03.849437+00:00
-- url     : https://prove2.me/theorems/b8bb015d-10a0-4ce6-a3a3-25033cf8fdad
-- title:
--   QECCertificates: mem light Cand
-- statement:
--   The QECCertificates construction uses the mem light Cand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L113-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L113-L117

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_lightCand {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightCand M₁ M₂ d ↔ v ∈ lightVecs n (d - 1) ∧ IsLightUndetectable M₁ M₂ v := by sorry
