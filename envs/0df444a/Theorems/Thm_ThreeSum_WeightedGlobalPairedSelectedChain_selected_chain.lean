-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedSelectedChain_selected_chain
-- name    : ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:21.633138+00:00
-- url     : https://prove2.me/theorems/adce8daa-cb64-450c-aac4-88d446eb8556
-- title:
--   Weighted Global Paired Selected Chain: selected chain
-- statement:
--   One complete selected chain. Its three inequalities are exactly the
--   ones established by the actual selector receipt above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L75-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L75-L101

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

theorem ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain (K m n b : ℕ) (hk : 0<K) (hm : 0<m) (hn : 1<n)
    (hF : (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m)
    (hp9 : 9<nativePrime K m)
    (Pi B C : ℕ→ℕ)
    (hstepPi : ∀ j, nativePrime K m^(2*K)*Pi (j+1)≤
      (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)*Pi j)
    (hstepB : ∀ j, nativePrime K m*B (j+1)≤9*B j)
    (hstepC : ∀ j, nativePrime K m*C (j+1)≤9*C j)
    (hinit : (Pi 0)^4≤((2*K).factorial*b^(2*K))^8*n^(8*K+5))
    (hinitB : B 0≤n^2) (hinitC : C 0≤n^2)
    (hnlarge : ((2*K).factorial*b^(2*K))^8<n)
    (hrate : WeightedGlobalPairedCollisionRate.charge K m<(7483/10000 : ℝ)) :
    Pi (radixLength m n)=0 ∧
      (B (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
      (C (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by sorry
