-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedSelectedChain_actual_good_step
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.actual_good_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:34:43.390149+00:00
-- url     : https://prove2.me/theorems/70377eff-5086-43cd-96cb-52a6cfd9fd65
-- title:
--   actual_good_step
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L53-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L53-L71

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.actual_good_step (a b p oldPi nextPi oldB nextB oldC nextC sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext)
    (flag vPi vB vC : ℕ→ℤ) (chosen : ℕ)
    (hPi : vPi chosen=(sNext*nextPi : ℕ))
    (hB : vB chosen=(nextB : ℕ)) (hC : vC chosen=(nextC : ℕ))
    (hgood : LightTernaryRowSelector.Good flag vPi vB vC (a*sOld) p p
      (b*sNext*(sOld*oldPi)) (9*oldB) (9*oldC) chosen) :
    a*nextPi≤b*oldPi ∧ p*nextB≤9*oldB ∧ p*nextC≤9*oldC := by sorry
