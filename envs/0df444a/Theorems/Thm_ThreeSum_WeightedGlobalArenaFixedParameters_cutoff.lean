-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:07:54.249129+00:00
-- url     : https://prove2.me/theorems/ade71397-97a4-4855-9077-4629522f0027
-- title:
--   Weighted Global Arena Fixed Parameters: cutoff
-- statement:
--   For the literal padded digit length, the actual requester/carry count
--   has the required fourth-power initial bound. All constants precede the input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L75-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L75-L102

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

theorem ThreeSum.WeightedGlobalArenaFixedParameters.cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix)
    {κ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m radix κ<microAllowance K)
    (U : ℕ→ℕ) (hU : ∀n,1<n→(U n : ℝ)≤(n : ℝ)^κ) :
    ∃n0 : ℕ,∀n≥n0,
      let r := radixLength m n
      let J := paddedLength radix (U n) r
      1<n ∧ r<J ∧ 4*U n<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by sorry
