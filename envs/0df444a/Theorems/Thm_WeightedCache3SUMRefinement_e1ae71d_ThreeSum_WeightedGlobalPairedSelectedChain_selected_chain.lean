-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedSelectedChain_selected_chain
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:34:03.484307+00:00
-- url     : https://prove2.me/theorems/2fcf043a-738b-475b-baa5-66285c413d15
-- title:
--   selected_chain
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L75-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L75-L101

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedSelectedChain
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial WeightedGlobalPairedNativeDrift
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalLocalParameters TernaryCoverLocal
open WeightedGlobalEntropyRates
open WeightedGlobalSignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.selected_chain (K m n b : ℕ) (hk : 0<K) (hm : 0<m) (hn : 1<n)
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
