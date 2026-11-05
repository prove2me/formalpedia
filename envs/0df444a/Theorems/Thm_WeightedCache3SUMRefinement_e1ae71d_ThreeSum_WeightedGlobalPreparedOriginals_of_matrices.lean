-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPreparedOriginals_of_matrices
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals.of_matrices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:36.248195+00:00
-- url     : https://prove2.me/theorems/3ad89d48-e53f-44a0-9aa9-2466d85d2c61
-- title:
--   of_matrices
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L57-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L57-L133

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals.of_matrices (free n U J radix C0 weightCap queryTime menu seedCount : ℕ)
    (A B C : List ℤ) (μ : ℕ→ℤ) (M : Matrices μ free n U J radix A B C)
    (hA : A.length≤n) (hb : 1<radix) (hp : radix<p)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (hmenuEnd : menu+seedCount*(J+2)≤free)
    (hmenu : ∀ordinal<seedCount,∀(k : ℕ)(hk : k<J+2), μ (menu+ordinal*(J+2)+k)=
      (TernaryOriginalRowMenu.seedRow (J+2) ℓ (seeds ordinal) (digitOrder J ⟨k,hk⟩)).val) :
    WeightedGlobalArenaPrefixInputs.Originals (input free n U J C0 weightCap queryTime A B C)
      (inputs free n J menu A B C) seedCount radix radix n ℓ seeds
      (left U radix J (fun i => B.getD i 0)) (right U radix J (fun i => C.getD i 0))
      (requester U radix J (fun i => A.getD i 0)) μ := by sorry
