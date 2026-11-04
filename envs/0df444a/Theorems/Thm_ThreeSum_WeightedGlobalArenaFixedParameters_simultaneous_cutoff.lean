-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_simultaneous_cutoff
-- name    : ThreeSum.WeightedGlobalArenaFixedParameters.simultaneous_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:08:05.593063+00:00
-- url     : https://prove2.me/theorems/522aedd3-d7d4-470e-bc73-c0afa610a5b7
-- title:
--   Weighted Global Arena Fixed Parameters: simultaneous cutoff
-- statement:
--   A single fixed choice, before any input is inspected, provides every
--   paired, original-collision, signed-preprocessing and terminal guard.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L133-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaFixedParameters.lean#L133-L149

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

theorem ThreeSum.WeightedGlobalArenaFixedParameters.simultaneous_cutoff {K : ℕ} (hK : 100000000000000000000≤K) (κ c d N : ℕ) :
    ∃t m n0 : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) (κ : ℝ)<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) ∧
      ∀n≥n0,InputGuards K m (2^t) κ n := by sorry
