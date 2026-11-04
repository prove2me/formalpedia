-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_natural_cutoff
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.natural_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:07:40.082537+00:00
-- url     : https://prove2.me/theorems/6604b2cd-222f-4a77-83ec-910c9a43fcef
-- title:
--   Weighted Global Arena Fixed Parameters: natural cutoff
-- statement:
--   The cutoff is phrased in exactly the dimensions produced by the actual
--   prelude, with its computed magnitude bound n^κ.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L106-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L106-L118

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalArenaFixedParameters.natural_cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix) (κ : ℕ)
    (hcarry : carryExponent m radix (κ : ℝ)<microAllowance K) :
    ∃n0 : ℕ,∀n≥n0,
      let r := LightWeightedGlobalDimensions.r (outputSize m) n
      let J := LightWeightedGlobalDimensions.J (outputSize m) radix n (n^κ)
      1<n ∧ r<J ∧ 4*n^κ<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by sorry
