-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_Uniform_mono
-- name    : ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:55:31.037614+00:00
-- url     : https://prove2.me/theorems/470a3763-7a54-4c98-a5c1-cd40001d6783
-- title:
--   Uniform: mono
-- statement:
--   The Uniform construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L59-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L59-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
attribute [local semireducible] Uniform

theorem ThreeSum.WeightedGlobalArenaPrefixFootprints.Uniform.mono {M : ℕ} {f g : ℕ→ℕ→ℕ→ℕ}
    (hg : Uniform M g) (h : ∀ n U j, j≤Nat.clog M (n^2) → f n U j≤g n U j) : Uniform M f := by sorry
