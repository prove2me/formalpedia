-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPreparedOriginals_metadata
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals.metadata
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:11:37.099679+00:00
-- url     : https://prove2.me/theorems/6a2195a7-1096-4f11-b79d-d5c9d60a7dbe
-- title:
--   metadata
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L154-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L154-L184

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPreparedOriginals.metadata {n U free : ℕ} (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (A B C : List ℤ) (μ : ℕ→ℤ)
    (hA : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.av free n) n
      (ColorClassLists.classList color x 0 1) A)
    (hB : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.bv free n) n
      (ColorClassLists.classList color x 1 1) B)
    (hC : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.cv free n) n
      (ColorClassLists.classList color x 2 (-1)) C)
    (hx : ∀i,|x i|≤(U:ℤ)) : Metadata n U A B C := by sorry
