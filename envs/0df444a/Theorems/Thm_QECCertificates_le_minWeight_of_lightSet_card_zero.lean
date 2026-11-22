-- Prove2me | Theorems.Thm_QECCertificates_le_minWeight_of_lightSet_card_zero
-- name    : QECCertificates.le_minWeight_of_lightSet_card_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:50.554807+00:00
-- url     : https://prove2.me/theorems/42734d02-a22e-4f41-808e-cde691dd636f
-- title:
--   QECCertificates: le min Weight of light Set card zero
-- statement:
--   **The lower-bound theorem, checkable certificate form**: an empty `lightSet` gives the
--   distance lower bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L156-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L156-L160

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

theorem QECCertificates.le_minWeight_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (h : (lightSet M₁ M₂ d).card = 0) :
    d ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by sorry
