-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_of_matrices
-- name    : ThreeSum.WeightedGlobalPreparedOriginals.of_matrices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:06:17.377872+00:00
-- url     : https://prove2.me/theorems/0649ca67-eb1f-40be-8392-988f303f424e
-- title:
--   Weighted Global Prepared Originals: of matrices
-- statement:
--   Every original signed/tagged row and every requester/carry row is read
--   from the concrete preprocessing matrices, with all endpoints proved.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L57-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L57-L133

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalPreparedOriginals.of_matrices (free n U J radix C0 weightCap queryTime menu seedCount : ℕ)
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
