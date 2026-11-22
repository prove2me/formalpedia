-- Prove2me | Theorems.Thm_QECCertificates_lowerHyp_of_lightSet_card_zero
-- name    : QECCertificates.lowerHyp_of_lightSet_card_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:10.665587+00:00
-- url     : https://prove2.me/theorems/88c48080-0c59-4331-a96f-8248aac6a6ac
-- title:
--   QECCertificates: lower Hyp of light Set card zero
-- statement:
--   **The lower-bound certificate, checkable form**: an empty set of light operators
--   implies that the code distance is at least `d`.
--
--   The proof is contraposition, coverage and translation. If an undetectable operator of
--   weight below `d` existed, its weight would be nonzero, since otherwise it would lie in
--   the row space and contradict undetectability, and a weight $\le d-1$ places it in the
--   weight-bounded enumeration (`mem_lightVecs`; **the soundness of this certificate rests
--   entirely on that coverage theorem**). The lemmas `inKerB_iff` and `inSpanEch_eq_false_iff`
--   then translate it into the two certificates of the decision layer, and `mem_lightCand`
--   puts it back into the set, contradicting emptiness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L131-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/LowerBound.lean#L131-L152

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

theorem QECCertificates.lowerHyp_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : (lightSet M₁ M₂ d).card = 0) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d ≤ hammingNorm E := by sorry
