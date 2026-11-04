-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_metadata
-- name    : ThreeSum.WeightedGlobalPreparedOriginals.metadata
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:04:01.04505+00:00
-- url     : https://prove2.me/theorems/c676b399-6ddc-411a-bcd5-62d8b5c82062
-- title:
--   Weighted Global Prepared Originals: metadata
-- statement:
--   The Weighted Global Prepared Originals construction uses the metadata property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L154-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L154-L184

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

theorem ThreeSum.WeightedGlobalPreparedOriginals.metadata {n U free : ℕ} (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (A B C : List ℤ) (μ : ℕ→ℤ)
    (hA : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.av free n) n
      (ColorClassLists.classList color x 0 1) A)
    (hB : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.bv free n) n
      (ColorClassLists.classList color x 1 1) B)
    (hC : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.cv free n) n
      (ColorClassLists.classList color x 2 (-1)) C)
    (hx : ∀i,|x i|≤(U:ℤ)) : Metadata n U A B C := by sorry
