-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_reads
-- name    : ThreeSum.WeightedGlobalArenaPrefixInputs.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T00:04:24.537011+00:00
-- url     : https://prove2.me/theorems/126fbfaf-4666-4a64-8fc1-76fe642cef3b
-- title:
--   Weighted Global Arena Prefix Inputs: reads
-- statement:
--   The retained prefix state supplies all old-key and span reads. Every
--   other read is transported from the actual immutable initialization.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInputs.lean#L36-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrefixInputs.lean#L36-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixState
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPreparedMemory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedDataReads
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateGuardAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixInputs
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedDataReads_reads
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixInputs
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation
open TernaryOriginalRowMenu WeightedGlobalNativeCompleteFrontend
open TernaryExtensionEncoding
open LightWeightedGlobalSeedScoreFactory
variable {p m F : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaPrefixInputs.reads (I : Input) (A : Inputs) (j featureBound tagBound positionCap seedCount ordinal : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (H : WeightedGlobalArenaPrefixState.Memory I A (fun i t => L i t.val) (fun i t => R i t.val)
      (fun i t => O i t.val) j s catalog initial μ)
    (hi : ordinal<seedCount) :
    WeightedGlobalArenaSeedPrimitiveGuards.Reads I A ordinal
      (data I A j featureBound ordinal ℓ (seeds ordinal) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) μ positionCap := by sorry
