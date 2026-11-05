-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaInitialSeedHeader_replacement
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaInitialSeedHeader.replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:46.111898+00:00
-- url     : https://prove2.me/theorems/80d4b185-50e7-4c70-8974-19c79a4ef9ad
-- title:
--   replacement
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L27-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L27-L53

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaInitialSeedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaInitialSeedHeader.replacement {μ ν : ℕ→ℤ} {seed : ℕ} {xs : List ℤ} {dB dC dP tB tC tP : ℕ}
    (hs : Seg μ seed xs) (hlen : xs.length=48)
    (hb : Seg ν (seed+41) (LightTernaryBudgetStep.oldValues dB dC dP tB tC tP))
    (hk : ∀x,x<seed+48→(x<seed+41 ∨ seed+47≤x)→ν x=μ x) :
    Seg ν seed (replace xs dB dC dP tB tC tP) := by sorry
