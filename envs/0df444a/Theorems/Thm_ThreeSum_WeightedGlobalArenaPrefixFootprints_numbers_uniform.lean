-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_numbers_uniform
-- name    : ThreeSum.WeightedGlobalArenaPrefixFootprints.numbers_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:57:33.533314+00:00
-- url     : https://prove2.me/theorems/4bf51ade-44d6-4c31-be9d-c40a8b1bb34c
-- title:
--   Weighted Global Arena Prefix Footprints: numbers uniform
-- statement:
--   The bound is uniform in the actual original magnitude and all prefixes;
--   all alphabets and circuit degrees are fixed by the compiled program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L317-L463
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L317-L463

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
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

open Lean Elab Tactic Meta

theorem ThreeSum.WeightedGlobalArenaPrefixFootprints.numbers_uniform {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    Uniform M (total maps τ cap M b K H drift scale) := by sorry
