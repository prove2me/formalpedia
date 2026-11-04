-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixState_final_transition
-- name    : ThreeSum.WeightedGlobalArenaPrefixState.final_transition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:25:49.330078+00:00
-- url     : https://prove2.me/theorems/d85414a4-20dd-45bb-ae71-03b4f5157bca
-- title:
--   Weighted Global Arena Prefix State: final transition
-- statement:
--   Root's concrete canonical Plan.Final receipt discharges the complete
--   selected-state memory transition after the actual commit.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L240-L272
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixState.lean#L240-L272

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
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
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixState
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalArenaSeedData WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaBudgetExistence WeightedGlobalArenaFamilyBudget
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaPrefixState.final_transition (maps : Fin F→WeightedGlobalCoverGoodMaps.Weight m p)
    (τ cap U V scoreBound U' : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 Rb Sb : ℕ) (e : (E×E)≃Fin N)
    (ℓ : E→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ) (raws : List ℤ) (words localMaps : List ℕ)
    (initial μ ζ ν : ℕ→ℤ)
    (hmem : Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j) catalog initial μ)
    (hL : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+L i t.val)
    (hR : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+R i t.val)
    (hO : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+O i t.val)
    (hcapacity : A.J*(p^j)*p≤I.capacity) :
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j
    let Ds := fun k => data I A j b k ℓ (seedAt e k) s.row
      (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog
    let f := WeightedGlobalArenaControllerCore.family maps τ cap U' Q I A Ds L R
    let ordinal := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1
    WeightedGlobalArenaControllerPlan.Final I f K Rb Sb ordinal (addr I.free I.capacity 8)
      raws words localMaps μ ζ→
    LightWeightedGlobalPrefixFinish.Committed (config p (j+1) I A 0) (p^(j+1)) (addr I.free I.capacity 8) ζ ν→
    ∃catalog', Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) (j+1)
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs (j+1)) catalog' initial ν := by sorry
