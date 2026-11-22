-- Prove2me | Theorems.Thm_QECCertificates_lightSet_card_le
-- name    : QECCertificates.lightSet_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:40.530797+00:00
-- url     : https://prove2.me/theorems/4813ef24-e2e0-402a-bcd7-de152c6e7eaf
-- title:
--   QECCertificates: light Set card le
-- statement:
--   The same statement in `Finset` form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L246-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L246-L250

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

theorem QECCertificates.lightSet_card_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightSet M₁ M₂ d).card ≤ ∑ k ∈ Finset.range d, n.choose k := by sorry
