-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPairedSelectedChain_actual_pick_positive
-- name    : ThreeSum.WeightedGlobalPairedSelectedChain.actual_pick_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:57.523998+00:00
-- url     : https://prove2.me/theorems/9ecf1f56-b83d-4b27-b8de-5fa4e179a783
-- title:
--   Weighted Global Paired Selected Chain: actual pick positive
-- statement:
--   The existence theorem feeds the literal scan used by the executable
--   selector. Every candidate is checked with its real admissibility bit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L25-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPairedSelectedChain.lean#L25-L49

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

theorem ThreeSum.WeightedGlobalPairedSelectedChain.actual_pick_positive {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (f : Fin 3→Fin N→ℕ) (num den : Fin 3→ℕ) (hd : ∀ i, 0<den i)
    (havg : ∀ i, den i*(∑ seed∈S, f i seed)≤3*S.card*num i)
    (flag : ℕ→ℤ) (values : Fin 3→ℕ→ℤ)
    (hflag : ∀ i : Fin N, flag i.val≠0 ↔ i∈S)
    (hvalues : ∀ j (i : Fin N), values j i.val=(f j i : ℤ)) :
    let good := LightTernaryRowSelector.Good flag (values 0) (values 1) (values 2)
      (den 0) (den 1) (den 2) (9*num 0) (9*num 1) (9*num 2)
    0<LightTernaryRowSelector.pick good N ∧
      good (LightTernaryRowSelector.pick good N-1) := by sorry
