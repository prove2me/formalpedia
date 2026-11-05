-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_prepared_good
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.prepared_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:42.303001+00:00
-- url     : https://prove2.me/theorems/445a9307-cbb3-4791-a7f3-6ca64c2e092b
-- title:
--   prepared_good
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L88-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaPhaseBudget.lean#L88-L136

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhase
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSelectedBudgets
open WeightedGlobalArenaSeedData WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryExtensionEncoding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaPhaseBudget.prepared_good (maps : Fin F→Weight m p) (τ cap V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (free n U radix K C0 weightCap queryTime menu j : ℕ)
    (A B C : List ℤ) (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hmeta : WeightedGlobalPreparedOriginals.Metadata n U A B C)
    (hK : 0<K) (hb : 1<radix) (hp : 2*radix<p) (hℓ : ℓ≠0)
    (hdet : (2*K).factorial*radix^(2*K)<p)
    (hj : j<LightWeightedGlobalDimensions.r (WeightedGlobalCoverScale.outputSize m) n)
    (hcard : Fintype.card E=p^(menuDegree p
      (LightWeightedGlobalDimensions.J (WeightedGlobalCoverScale.outputSize m) radix n U+2) K)) :
    let J := LightWeightedGlobalDimensions.J (WeightedGlobalCoverScale.outputSize m) radix n U
    let I := WeightedGlobalPreparedOriginals.input free n U J C0 weightCap queryTime A B C
    let AP := WeightedGlobalPreparedOriginals.inputs free n J menu A B C
    let L := WeightedGlobalArenaSelectedSigned.left U radix J (fun i => B.getD i 0)
    let R := WeightedGlobalArenaSelectedSigned.right U radix J (fun i => C.getD i 0)
    let O := WeightedGlobalArenaSelectedSigned.requester U radix J (fun i => A.getD i 0)
    let U0 := LightTernaryInitialBudgets.initial K radix n J (A.length*2^J)
    let s := run maps τ cap U V scoreBound Q I AP radix K n U0 e ℓ L R O catalogs j
    ∃i<N,LightTernaryRowSelector.Good
      (WeightedGlobalArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).flag
      (WeightedGlobalArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreB
      (WeightedGlobalArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreC
      ((WeightedGlobalArenaPhase.family maps τ cap radix Q I AP j radix ℓ (seedAt e) L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1)) i := by sorry
