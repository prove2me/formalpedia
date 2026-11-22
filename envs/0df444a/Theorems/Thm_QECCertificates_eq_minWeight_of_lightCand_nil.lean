-- Prove2me | Theorems.Thm_QECCertificates_eq_minWeight_of_lightCand_nil
-- name    : QECCertificates.eq_minWeight_of_lightCand_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:25.236143+00:00
-- url     : https://prove2.me/theorems/3b98c4a7-e8c9-4fb1-802d-307b5180e55b
-- title:
--   QECCertificates: eq min Weight of light Cand nil
-- statement:
--   **The exact distance, List form**: the same shape as `eq_minWeight_of_decide` with the
--   lower-bound hypothesis replaced by an empty candidate list; used for instances with large
--   candidate sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L203-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L203-L209

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

theorem QECCertificates.eq_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : lightCand M₁ M₂ d = []) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d := by sorry
