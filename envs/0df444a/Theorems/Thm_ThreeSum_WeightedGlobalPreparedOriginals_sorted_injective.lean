-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_sorted_injective
-- name    : ThreeSum.WeightedGlobalPreparedOriginals.sorted_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:59:11.732185+00:00
-- url     : https://prove2.me/theorems/f155da75-d22c-453e-9a7c-8b03e0287741
-- title:
--   Weighted Global Prepared Originals: sorted injective
-- statement:
--   The Weighted Global Prepared Originals construction uses the sorted injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L145-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L145-L152

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

theorem ThreeSum.WeightedGlobalPreparedOriginals.sorted_injective (L : List ℤ) (h : L.Pairwise (· < ·)) :
    Function.Injective (fun i : Fin L.length => L.getD i.val 0) := by sorry
