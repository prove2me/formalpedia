-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixPrepareAllocation_envelope_bound
-- name    : ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.envelope_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:26:13.168413+00:00
-- url     : https://prove2.me/theorems/d71738d2-e56a-4e45-9bfd-db56ac315ada
-- title:
--   Weighted Global Arena Prefix Prepare Allocation: envelope bound
-- statement:
--   The actual dynamic preparation envelope contains no address advice.
--   Its scalar values fit the explicit fixed header footprint at the new prefix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L42-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixPrepareAllocation.lean#L42-L162

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepare
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixPrepareAllocation.envelope_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j U0 : ℕ)
    (I : Input) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (hscale : 1≤drift*scale)
    (hU0 : U0≤LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightWeightedGlobalDimensions.J M b n U) (n*2^(LightWeightedGlobalDimensions.J M b n U))) :
    WeightedGlobalArenaPrefixPrepare.envelope
      (WeightedGlobalArenaPrefixPrepare.inputs p m F j (LightWeightedGlobalDimensions.J M b n U) n U0
        (p^(2*K)) drift scale I Q)≤
      (numbers maps τ cap M b K H drift scale n U (j+1)).prefixCells+
        (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader := by sorry
