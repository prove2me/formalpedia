-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedSelectedChain_actual_good_step
-- name    : ThreeSum.WeightedGlobalPairedSelectedChain.actual_good_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:53:17.908683+00:00
-- url     : https://prove2.me/theorems/9affdce8-266e-46dc-9395-91e5aaa69211
-- title:
--   Weighted Global Paired Selected Chain: actual good step
-- statement:
--   Semantics of the physical selector give the unscaled paired and both
--   original-source collision contractions. Query factorials cancel exactly.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L53-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L53-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryPairedSelectedChain
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.WeightedGlobalPairedSelectedChain.actual_good_step (a b p oldPi nextPi oldB nextB oldC nextC sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext)
    (flag vPi vB vC : ℕ→ℤ) (chosen : ℕ)
    (hPi : vPi chosen=(sNext*nextPi : ℕ))
    (hB : vB chosen=(nextB : ℕ)) (hC : vC chosen=(nextC : ℕ))
    (hgood : LightTernaryRowSelector.Good flag vPi vB vC (a*sOld) p p
      (b*sNext*(sOld*oldPi)) (9*oldB) (9*oldC) chosen) :
    a*nextPi≤b*oldPi ∧ p*nextB≤9*oldB ∧ p*nextC≤9*oldC := by sorry
