-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixInputs_Originals_of_kept
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs.Originals.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:23.100078+00:00
-- url     : https://prove2.me/theorems/a5b76476-ff5c-4459-bf93-a5bf332c2575
-- title:
--   of_kept
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaOriginalInputs.lean#L53-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaOriginalInputs.lean#L53-L66

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Theorems.Thm_Light_Seg_of_kept

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData TernaryExtensionEncoding
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPrefixInputs.Originals.of_kept {I : Input} {A : Inputs} {seedCount featureBound tagBound positionCap : ℕ}
    {ℓ : E→ₗ[ZMod p] ZMod p} {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ ν : ℕ→ℤ}
    (H : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O μ)
    (hk : Kept μ ν I.free) : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O ν := by sorry
