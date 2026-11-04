-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedSelectedChain_selected_chain_eventually
-- name    : ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:53:27.329136+00:00
-- url     : https://prove2.me/theorems/097a958b-a22a-4aca-88f6-425b3421f83b
-- title:
--   Weighted Global Paired Selected Chain: selected chain eventually
-- statement:
--   The initial score is the literal sum of original endpoint minors over
--   requester/carry groups. The executable selected inequalities then force
--   zero paired score and the paid collision bounds for every large input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L106-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L106-L136

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

theorem ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain_eventually {K m b : ℕ} (hk : 0<K) (hm : 0<m) (hb : 1<b)
    {κ δ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m b κ<δ) (hδ : 4*δ<1)
    (hF : (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m)
    (hp9 : 9<nativePrime K m)
    (hrate : WeightedGlobalPairedCollisionRate.charge K m<(7483/10000 : ℝ))
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ)
    (P G : ℕ→Type*) [∀ n, Fintype (P n)] [∀ n, Fintype (G n)]
    (A : ∀ n, G n→(Fin K→P n)→Matrix (Fin (2*K))
      (Fin (paddedLength b (U n) (radixLength m n)+2)) ℤ)
    (hA : ∀ n g e i j, (A n g e i j).natAbs≤b)
    (hG : ∀ n, Fintype.card (G n)≤n*2^(paddedLength b (U n) (radixLength m n)))
    (hP : ∀ n, Fintype.card (P n)≤n^2)
    (Pi B C : ℕ→ℕ→ℕ)
    (hPi0 : ∀ n, Pi n 0≤∑ g : G n, ∑ e : Fin K→P n, minorWeight (A n g e))
    (hB0 : ∀ n, B n 0≤n^2) (hC0 : ∀ n, C n 0≤n^2)
    (hstepPi : ∀ n j, nativePrime K m^(2*K)*Pi n (j+1)≤
      (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)*Pi n j)
    (hstepB : ∀ n j, nativePrime K m*B n (j+1)≤9*B n j)
    (hstepC : ∀ n j, nativePrime K m*C n (j+1)≤9*C n j) :
    ∀ᶠ n : ℕ in atTop,
      Pi n (radixLength m n)=0 ∧
      (B n (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
      (C n (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by sorry
