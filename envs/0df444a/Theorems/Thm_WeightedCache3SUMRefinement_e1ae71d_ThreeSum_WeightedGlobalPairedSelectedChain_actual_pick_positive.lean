-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPairedSelectedChain_actual_pick_positive
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.actual_pick_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:34:27.744775+00:00
-- url     : https://prove2.me/theorems/0324313b-52fd-42b6-9187-35a147266f52
-- title:
--   actual_pick_positive
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L25-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L25-L49

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedSelectedChain.actual_pick_positive {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (f : Fin 3→Fin N→ℕ) (num den : Fin 3→ℕ) (hd : ∀ i, 0<den i)
    (havg : ∀ i, den i*(∑ seed∈S, f i seed)≤3*S.card*num i)
    (flag : ℕ→ℤ) (values : Fin 3→ℕ→ℤ)
    (hflag : ∀ i : Fin N, flag i.val≠0 ↔ i∈S)
    (hvalues : ∀ j (i : Fin N), values j i.val=(f j i : ℤ)) :
    let good := LightTernaryRowSelector.Good flag (values 0) (values 1) (values 2)
      (den 0) (den 1) (den 2) (9*num 0) (9*num 1) (9*num 2)
    0<LightTernaryRowSelector.pick good N ∧
      good (LightTernaryRowSelector.pick good N-1) := by sorry
