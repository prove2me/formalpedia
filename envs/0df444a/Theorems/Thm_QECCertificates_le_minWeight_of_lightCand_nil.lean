-- Prove2me | Theorems.Thm_QECCertificates_le_minWeight_of_lightCand_nil
-- name    : QECCertificates.le_minWeight_of_lightCand_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:20.620806+00:00
-- url     : https://prove2.me/theorems/353dd7a6-9e86-4773-8541-383c30b14dbf
-- title:
--   QECCertificates: le min Weight of light Cand nil
-- statement:
--   **The lower-bound theorem, List form**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L194-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L194-L198

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

theorem QECCertificates.le_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d₀ : ℕ} (hd : d₀ ≤ n) (h : lightCand M₁ M₂ d₀ = []) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by sorry
