-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_fixed_capacity
-- name    : ThreeSum.WeightedGlobalArenaPrefixFootprints.fixed_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:56:42.374817+00:00
-- url     : https://prove2.me/theorems/94dad247-d768-49f0-bad0-b45cf0d985d2
-- title:
--   Weighted Global Arena Prefix Footprints: fixed capacity
-- statement:
--   These are universal compile-time constants for every literal entry of
--   our actual prefix footprint list, rather than a resource-oracle premise.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L486-L499
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixFootprints.lean#L486-L499

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

theorem ThreeSum.WeightedGlobalArenaPrefixFootprints.fixed_capacity {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    ∃ D E : ℕ, ∀ n U j, j≤Nat.clog M (n^2) →
      ∀ v∈(numbers maps τ cap M b K H drift scale n U j).list,
        v≤capacity D E (n+U) := by sorry
