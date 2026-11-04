-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_Originals_of_kept
-- name    : ThreeSum.WeightedGlobalArenaPrefixInputs.Originals.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:26:20.460001+00:00
-- url     : https://prove2.me/theorems/57c03997-7862-49d9-939e-765eda3d1dc1
-- title:
--   Originals: of kept
-- statement:
--   Actual arena/header initialization preserves the original prefix
--   certificate whenever it keeps all cells before the arena free pointer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaOriginalInputs.lean#L53-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaOriginalInputs.lean#L53-L66

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Theorems.Thm_Light_Seg_of_kept

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixInputs
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData TernaryExtensionEncoding
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPrefixInputs.Originals.of_kept {I : Input} {A : Inputs} {seedCount featureBound tagBound positionCap : ℕ}
    {ℓ : E→ₗ[ZMod p] ZMod p} {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ ν : ℕ→ℤ}
    (H : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O μ)
    (hk : Kept μ ν I.free) : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O ν := by sorry
