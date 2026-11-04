-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTerminalReceipt_source_input_signed
-- name    : ThreeSum.WeightedGlobalArenaTerminalReceipt.source_input_signed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:07:39.627136+00:00
-- url     : https://prove2.me/theorems/a3dd3dd1-8ec1-4997-ad2b-abe38eeb66d8
-- title:
--   Weighted Global Arena Terminal Receipt: source input signed
-- statement:
--   Exact final-solver semantic input, with every actual requester/carry
--   occurrence retained. This is an equality of functions, not bounded samples.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L53-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTerminalReceipt.lean#L53-L75

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalSolver
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTerminalReceipt
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_Resources_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_Resources_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTerminalReceipt
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open WeightedGlobalArenaSelectedSigned WeightedGlobalArenaSelectedTerminal WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaTerminalReceipt.source_input_signed (maps : Fin F→Weight m p) (τ cap U V scoreBound tag : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (j radix K n nA U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (X B C : ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hb : 1<radix) (hp : radix≤p) (hbase : WeightedGlobalArenaSelectedSigned.base I A.J nA=I) :
    let L := left U radix A.J B
    let R := right U radix A.J C
    let O := requester U radix A.J X
    let s := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs j
    let f := WeightedGlobalArenaPhase.family maps τ cap tag Q I A j radix ℓ (seedAt e) L R O s catalog
    let i := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1))-1
    let s' := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs (j+1)
    sourceInput I A i (f.candidate i).data=
      WeightedGlobalArenaNativeComplete.input I U radix nA (selectedHash A s' (j+1)) X B C := by sorry
