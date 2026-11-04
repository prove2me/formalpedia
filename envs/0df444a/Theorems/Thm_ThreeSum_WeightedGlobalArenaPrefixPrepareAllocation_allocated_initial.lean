-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_allocated_initial
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:22:00.954583+00:00
-- url     : https://prove2.me/theorems/59012e4c-80ac-4cda-bc3b-bf7dcfe693fc
-- title:
--   Weighted Global Arena Prefix Prepare Allocation: allocated initial
-- statement:
--   Specialization to the actual initialized paired threshold; the
--   requester-count cap is the only required input-size comparison.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L189-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L189-L200

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated_initial (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j nO : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U)) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j (LightWeightedGlobalDimensions.J M b n U) n
        (LightTernaryInitialBudgets.initial K b n (LightWeightedGlobalDimensions.J M b n U) nO)
        (p^(2*K)) drift scale I Q)≤I.capacity := by sorry
