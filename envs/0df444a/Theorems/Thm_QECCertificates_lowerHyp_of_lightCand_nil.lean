-- Prove2me | Theorems.Thm_QECCertificates_lowerHyp_of_lightCand_nil
-- name    : QECCertificates.lowerHyp_of_lightCand_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:14.262719+00:00
-- url     : https://prove2.me/theorems/8bd9aba3-6fc0-4cfe-88cd-90ef0935bd69
-- title:
--   QECCertificates: lower Hyp of light Cand nil
-- statement:
--   **The lower-bound certificate, List form**: an empty candidate list implies that the
--   code distance is at least `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L172-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L172-L191

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

theorem QECCertificates.lowerHyp_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : lightCand M₁ M₂ d = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d ≤ hammingNorm E := by sorry
