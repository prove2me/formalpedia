-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaInitialSeedHeader_initialized
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaInitialSeedHeader.initialized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:02.971608+00:00
-- url     : https://prove2.me/theorems/fe5ad72c-ffdd-41a7-a0db-352a2034349b
-- title:
--   initialized
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L72-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L72-L86

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaInitialSeedHeader.initialized {I : Input} {A : Inputs} {p q seed constants K bDigit n : ℕ}
    {μ ν : ℕ→ℤ}
    (hseed : seed=addr I.free I.capacity 2)
    (hconstants : seed+48≤constants)
    (hs : Seg μ seed (header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8)))
    (hb : Seg ν (seed+41) [1,1,1,((n*n:ℕ):ℤ),((n*n:ℕ):ℤ),
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount:ℤ)])
    (hk : ∀x,(x<seed+41 ∨ seed+47≤x)→(x<constants ∨ constants+3≤x)→ν x=μ x) :
    Seg ν seed (header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
      (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8)) := by sorry
