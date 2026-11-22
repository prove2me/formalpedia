-- Prove2me | Theorems.Thm_QECCertificates_mem_lightSet
-- name    : QECCertificates.mem_lightSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:31.256082+00:00
-- url     : https://prove2.me/theorems/f89d6da7-6b0c-4bdf-aa62-347b1d38274b
-- title:
--   QECCertificates: mem light Set
-- statement:
--   Membership characterization, expanding `lightSet` into the candidate set and the
--   predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L107-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L107-L111

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

theorem QECCertificates.mem_lightSet {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightSet M₁ M₂ d ↔ v ∈ lightCand M₁ M₂ d := by sorry
