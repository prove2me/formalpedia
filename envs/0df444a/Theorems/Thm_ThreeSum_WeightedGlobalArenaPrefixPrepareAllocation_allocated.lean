-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_allocated
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:24:38.368199+00:00
-- url     : https://prove2.me/theorems/044a98fc-2b71-42db-8233-1ed98463611f
-- title:
--   Weighted Global Arena Prefix Prepare Allocation: allocated
-- statement:
--   The fixed polynomial capacity selected once for all inputs and prefixes
--   supplies the dynamic header constructor's last scalar premise.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L166-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L166-L185

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaCandidateScoreBounds_allocated
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.allocated (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j U0 : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hU0 : U0≤LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightWeightedGlobalDimensions.J M b n U) (n*2^(LightWeightedGlobalDimensions.J M b n U))) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j (LightWeightedGlobalDimensions.J M b n U) n U0
        (p^(2*K)) drift scale I Q)≤I.capacity := by sorry
