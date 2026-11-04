-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedData_candidate_score
-- name    : ThreeSum.WeightedGlobalArenaSeedData.candidate_score
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:18:51.928262+00:00
-- url     : https://prove2.me/theorems/43790a50-bae5-40c0-a8dc-9e2bfe20e91c
-- title:
--   Weighted Global Arena Seed Data: candidate score
-- statement:
--   The Weighted Global Arena Seed Data construction uses the candidate score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L168-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSeedData.lean#L168-L190

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedData
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_rows
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightTernaryCountFrontend.rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedData
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory TernaryExtensionEncoding
open TernaryOriginalRowMenu
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem ThreeSum.WeightedGlobalArenaSeedData.candidate_score {m F : ℕ} (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (r b k K : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→ℕ→ℤ) (rows : List (Fin A.J→ZMod p)) (catalog : ℕ→ℕ→ℕ)
    (hR : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+R i t.val)
    (hO : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+O i t.val)
    (hLall : ∀ i : ℕ, ∀ t : Fin (A.J+2), 0≤(p : ℤ)+L i t.val) :
    (candidate maps τ cap U V scoreBound Q I A k
      (data I A r b k ℓ seed row (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) rows catalog) L R).score K=
      (2^(((r+1)*fixedPi m 2)*K)*
        WeightedGlobalArenaPrefixPotential.value maps τ cap I (fun i t => L i t.val) (fun i t => R i t.val)
          (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed))
          (root (Function.update row r (TernaryOriginalRowMenu.row (A.J+2) ℓ seed)) (fun i t => O i t.val)) Q (r+1) K : ℕ) := by sorry
